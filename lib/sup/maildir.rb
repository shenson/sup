require 'rmail'
require 'uri'

module Redwood

  ## Maildir doesn't provide an ordered unique id, which is what Sup
  ## requires to be really useful. So we must maintain, in memory, a
  ## mapping between Sup "ids" (timestamps, essentially) and the
  ## pathnames on disk.

  class Maildir < Source
    include SerializeLabelsNicely
    SCAN_INTERVAL = 30 # seconds
    MYHOSTNAME = Socket.gethostname

    ## remind me never to use inheritance again.
    yaml_properties :uri, :cur_offset, :usual, :archived, :id, :labels, :mtimes
    def initialize uri, last_date=nil, usual=true, archived=false, id=nil, labels=[], mtimes={}
      super uri, last_date, usual, archived, id
      uri = URI(Source.expand_filesystem_uri(uri))

      raise ArgumentError, "not a maildir URI" unless uri.scheme == "maildir"
      raise ArgumentError, "maildir URI cannot have a host: #{uri.host}" if uri.host
      raise ArgumentError, "maildir URI must have a path component" unless uri.path

      @dir = uri.path
      @labels = Set.new(labels || [])
      @ids = []
      @new_ids = []
      @new_len = 0
      @ids_to_fns = {}
      @ids_to_mtimes = {}
      @last_scan = nil
      self.cur_offset = 0 if self.cur_offset.nil?
      @mutex = Mutex.new
      #the mtime from the subdirs in the maildir with the unix epoch as default.
      #these are used to determine whether scanning the directory for new mail
      #is a worthwhile effort
      @mtimes = { 'cur' => Time.at(0), 'new' => Time.at(0) }.merge(mtimes || {})
    end

    def file_path; @dir end
    def self.suggest_labels_for path; [] end
    def is_source_for? uri; super || (URI(Source.expand_filesystem_uri(uri)) == URI(self.uri)); end

    def check
      raise FatalSourceError unless File.directory? @dir
    end

    def store_message date, from_email, &block
      stored = false
      new_fn = new_maildir_basefn + ':2'
      Dir.chdir(@dir) do |d|
        tmp_path = File.join(@dir, 'tmp', new_fn)
        new_path = File.join(@dir, 'new', new_fn)
        begin
          sleep 2 if File.stat(tmp_path)

          File.stat(tmp_path)
        rescue Errno::ENOENT #this is what we want.
          begin
            File.open(tmp_path, 'wb') do |f|
              yield f #provide a writable interface for the caller
              f.fsync
            end

            File.link tmp_path, new_path
            stored = true
          ensure
            File.unlink tmp_path if File.exists? tmp_path
          end
        end #rescue Errno...
      end #Dir.chdir

      stored
    end

    def each_raw_message_line id
      scan_mailbox
      with_file_for(id) do |f|
        until f.eof?
          yield f.gets
        end
      end
    end

    def load_header id
      scan_mailbox
      with_file_for(id) { |f| parse_raw_email_header f }
    end

    def load_message id
      scan_mailbox
      with_file_for(id) { |f| RMail::Parser.read f }
    end

    def raw_header id
      scan_mailbox
      ret = ""
      with_file_for(id) do |f|
        until f.eof? || (l = f.gets) =~ /^$/
          ret += l
        end
      end
      ret
    end

    def raw_message id
      scan_mailbox
      with_file_for(id) { |f| f.read }
    end

    def scan_mailbox opts={}
      return unless @last_scan.nil? || opts[:rescan]
      return if @last_scan && (Time.now - @last_scan) < SCAN_INTERVAL

      initial_poll = @last_scan.nil?

      @last_scan = Time.now

      debug "scanning maildir #@dir..."
      begin
        @ids_to_fns = {}
        @ids = []
        @new_ids = []

        debug "Finding messages sup knows about for source #@dir..."

        @mtimes.each_key do |d|
          subdir = File.join(@dir, d)
          raise FatalSourceError, "#{subdir} not a directory" unless File.directory? subdir

          mtime = File.mtime subdir

          #only scan the dir if the mtime is more recent (or we haven't polled
          #since startup)
          if @mtimes[d] < mtime || initial_poll
            @mtimes[d] = mtime
            Dir[File.join(subdir, '*')].map do |fn|
              id = make_id fn
              msgtime = File.mtime(fn).to_i
              @ids_to_fns[id] = fn
              @ids << id
              @ids_to_mtimes[id] = msgtime
              @new_ids << id if msgtime  > self.cur_offset
            end
          else
            debug "no poll on #{d}.  mtime on indicates no new messages."
          end
        end
      rescue SystemCallError, IOError => e
        raise FatalSourceError, "Problem scanning Maildir directories: #{e.message}."
      end

      @new_ids.sort!{ |a,b| @ids_to_mtimes[a] <=> @ids_to_mtimes[b] }
      @new_len = @new_ids.length

    end
    synchronized :scan_mailbox

    def each
      scan_mailbox
      return if @last_scan.nil?
      @new_ids.each do |id|
        self.cur_offset = File.mtime( id_to_fn id ).to_i
        @new_len -= 1
        yield id, @labels + (seen?(id) ? [] : [:unread]) + (trashed?(id) ? [:deleted] : []) + (flagged?(id) ? [:starred] : [])
      end
    end

    def start_offset
      0
    end

    def end_offset
      cur_offset.to_f / ( 1.0 - @new_len.to_f / @ids.length.to_f )
    end

    def done?
      not @last_scan.nil? and not @new_ids.empty?
    end

    def pct_done
      100.0 - 100.0 * (@new_len.to_f / @ids.length.to_f)
    end

    def reset!
      debug "reset called"
      self.cur_offset = 0
      @new_ids = @ids.sort{ |a,b| @ids_to_mtimes[a] <=> @ids_to_mtimes[b] }
      @new_len = @new_ids.length
    end

    def acked? msg; File.basename(File.dirname(id_to_fn(msg))) == 'cur'; end
    def draft? msg; maildir_data(msg)[2].include? "D"; end
    def flagged? msg; maildir_data(msg)[2].include? "F"; end
    def passed? msg; maildir_data(msg)[2].include? "P"; end
    def replied? msg; maildir_data(msg)[2].include? "R"; end
    def seen? msg; maildir_data(msg)[2].include? "S"; end
    def trashed? msg; maildir_data(msg)[2].include? "T"; end

    def mark_acked msg; maildir_mark_file msg, '' unless acked? msg; end
    def mark_draft msg; maildir_mark_file msg, "D" unless draft? msg; end
    def mark_flagged msg; maildir_mark_file msg, "F" unless flagged? msg; end
    def mark_passed msg; maildir_mark_file msg, "P" unless passed? msg; end
    def mark_replied msg; maildir_mark_file msg, "R" unless replied? msg; end
    def mark_seen msg; maildir_mark_file msg, "S" unless seen? msg; end
    def mark_trashed msg; maildir_mark_file msg, "T" unless trashed? msg; end

    def delete msg
      fn = id_to_fn msg
      @ids.delete(msg)
      @ids_to_fns.delete(msg)
      File.unlink fn
    end

    private

    def filename_for_id id; id_to_fn(id) end

    def make_id fn
      File.basename(fn).split(':')[0] unless fn.nil?
    end

    def id_to_fn id
      if @ids_to_fns.has_key? id
        @ids_to_fns[id]
      else
        @ids_to_fns[id] = find_id_to_fn id
      end
    end

    def find_id_to_fn id
      fns = Dir.glob(File.join(@dir,'cur',id)+'*')+Dir.glob(File.join(@dir,'new',id)+'*')
      fns[0] unless fns.empty?
    end

    def new_maildir_basefn
      Kernel::srand()
      "#{Time.now.to_i.to_s}.#{$$}#{Kernel.rand(1000000)}.#{MYHOSTNAME}"
    end

    def with_file_for id
      fn = id_to_fn(id) or raise OutOfSyncSourceError, "No such id: #{id.inspect}."
      begin
        begin
          File.open(fn, 'rb') { |f| yield f }
        rescue SystemCallError, IOError => e
          debug "ID lost FN: #{id}"
          fn = find_id_to_fn id
          @ids_to_fns[id] = fn
          raise FatalSourceError, "Problem reading file for id #{id.inspect}: No longer in Source." if fn.nil?
          File.open(fn, 'rb') { |f| yield f }
        end
      rescue SystemCallError, IOError => e
        raise FatalSourceError, "Problem reading file for id #{id.inspect}: #{fn.inspect}: #{e.message}."
      end
    end

    def maildir_data msg
      fn = id_to_fn(msg) or raise OutOfSyncSourceError, "No such id: #{id.inspect}."
      fn = File.basename fn
      fn =~ %r{^([^:]+):([12]),([DFPRST]*)$}
      [($1 || fn), ($2 || "2"), ($3 || "")]
    end

    ## not thread-safe on msg
    def maildir_mark_file msg, flag
      orig_path = id_to_fn(msg)
      orig_base, orig_fn = File.split(orig_path)
      new_base = orig_base.slice(0..-4) + 'cur'
      tmp_base = orig_base.slice(0..-4) + 'tmp'
      md_base, md_ver, md_flags = maildir_data msg
      md_flags += flag; md_flags = md_flags.split(//).sort.join.squeeze
      new_path = File.join new_base, "#{md_base}:#{md_ver},#{md_flags}"
      tmp_path = File.join tmp_base, "#{md_base}:#{md_ver},#{md_flags}"
      File.link orig_path, tmp_path
      File.unlink orig_path
      File.link tmp_path, new_path
      File.unlink tmp_path
      @ids_to_fns[msg] = new_path
    end
  end

end
