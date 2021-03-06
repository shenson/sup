module Redwood

class CryptoManager
  include Singleton

  class Error < StandardError; end

  OUTGOING_MESSAGE_OPERATIONS = OrderedHash.new(
    [:sign, "Sign"],
    [:sign_and_encrypt, "Sign and encrypt"],
    [:encrypt, "Encrypt only"]
  )

  HookManager.register "gpg-args", <<EOS
Runs before gpg is executed, allowing you to modify the arguments (most
likely you would want to add something to certain commands, like
--trust-model always to signing/encrypting a message, but who knows).

Variables:
args: arguments for running GPG

Return value: the arguments for running GPG
EOS

  def initialize
    @mutex = Mutex.new

    bin = `which gpg`.chomp
    @cmd = case bin
    when /\S/
      debug "crypto: detected gpg binary in #{bin}"
      "#{bin} --quiet --batch --no-verbose --logger-fd 1 --use-agent"
    else
      debug "crypto: no gpg binary detected"
      nil
    end
  end

  def have_crypto?; !@cmd.nil? end

  def sign from, to, payload
    payload_fn = Tempfile.new "redwood.payload"
    payload_fn.write format_payload(payload)
    payload_fn.close

    sig_fn = Tempfile.new "redwood.signature"; sig_fn.close

    message = run_gpg "--output #{sig_fn.path} --yes --armor --detach-sign --textmode --local-user '#{from}' #{payload_fn.path}", :interactive => true
    unless $?.success?
      info "Error while running gpg: #{message}"
      raise Error, "GPG command failed. See log for details."
    end

    envelope = RMail::Message.new
    envelope.header["Content-Type"] = 'multipart/signed; protocol=application/pgp-signature; micalg=pgp-sha1'

    envelope.add_part payload
    signature = RMail::Message.make_attachment IO.read(sig_fn.path), "application/pgp-signature", nil, "signature.asc"
    envelope.add_part signature
    envelope
  end

  def encrypt from, to, payload, sign=false
    payload_fn = Tempfile.new "redwood.payload"
    payload_fn.write format_payload(payload)
    payload_fn.close

    encrypted_fn = Tempfile.new "redwood.encrypted"; encrypted_fn.close

    recipient_opts = (to + [ from ] ).map { |r| "--recipient '<#{r}>'" }.join(" ")
    sign_opts = sign ? "--sign --local-user '#{from}'" : ""
    message = run_gpg "--output #{encrypted_fn.path} --yes --armor --encrypt --textmode #{sign_opts} #{recipient_opts} #{payload_fn.path}", :interactive => true
    unless $?.success?
      info "Error while running gpg: #{message}"
      raise Error, "GPG command failed. See log for details."
    end

    encrypted_payload = RMail::Message.new
    encrypted_payload.header["Content-Type"] = "application/octet-stream"
    encrypted_payload.header["Content-Disposition"] = 'inline; filename="msg.asc"'
    encrypted_payload.body = IO.read(encrypted_fn.path)

    control = RMail::Message.new
    control.header["Content-Type"] = "application/pgp-encrypted"
    control.header["Content-Disposition"] = "attachment"
    control.body = "Version: 1\n"

    envelope = RMail::Message.new
    envelope.header["Content-Type"] = 'multipart/encrypted; protocol="application/pgp-encrypted"'

    envelope.add_part control
    envelope.add_part encrypted_payload
    envelope
  end

  def sign_and_encrypt from, to, payload
    encrypt from, to, payload, true
  end

  def verify payload, signature # both RubyMail::Message objects
    return unknown_status(cant_find_binary) unless @cmd

    payload_fn = Tempfile.new "redwood.payload"
    payload_fn.write format_payload(payload)
    payload_fn.close

    signature_fn = Tempfile.new "redwood.signature"
    signature_fn.write signature.decode
    signature_fn.close

    output = run_gpg "--verify #{signature_fn.path} #{payload_fn.path}"
    output_lines = output.split(/\n/)

    if output =~ /^gpg: (.* signature from .*$)/
      if $? == 0
        Chunk::CryptoNotice.new :valid, $1, output_lines
      else
        Chunk::CryptoNotice.new :invalid, $1, output_lines
      end
    else
      unknown_status output_lines
    end
  end

  ## returns decrypted_message, status, desc, lines
  def decrypt payload # a RubyMail::Message object
    return unknown_status(cant_find_binary) unless @cmd

    payload_fn = Tempfile.new "redwood.payload"
    payload_fn.write payload.to_s
    payload_fn.close

    output_fn = Tempfile.new "redwood.output"
    output_fn.close

    message = run_gpg "--output #{output_fn.path} --yes --decrypt #{payload_fn.path}", :interactive => true

    unless $?.success?
      info "Error while running gpg: #{message}"
      return Chunk::CryptoNotice.new(:invalid, "This message could not be decrypted", message.split("\n"))
    end

    output = IO.read output_fn.path
    output.force_encoding Encoding::ASCII_8BIT if output.respond_to? :force_encoding

    ## there's probably a better way to do this, but we're using the output to
    ## look for a valid signature being present.

    sig = case message
    when /^gpg: (Good signature from .*$)/i
      Chunk::CryptoNotice.new :valid, $1, message.split("\n")
    when /^gpg: (Bad signature from .*$)/i
      Chunk::CryptoNotice.new :invalid, $1, message.split("\n")
    end

    # This is gross. This decrypted payload could very well be a multipart
    # element itself, as opposed to a simple payload. For example, a
    # multipart/signed element, like those generated by Mutt when encrypting
    # and signing a message (instead of just clearsigning the body).
    # Supposedly, decrypted_payload being a multipart element ought to work
    # out nicely because Message::multipart_encrypted_to_chunks() runs the
    # decrypted message through message_to_chunks() again to get any
    # children. However, it does not work as intended because these inner
    # payloads need not carry a MIME-Version header, yet they are fed to
    # RMail as a top-level message, for which the MIME-Version header is
    # required. This causes for the part not to be detected as multipart,
    # hence being shown as an attachment. If we detect this is happening,
    # we force the decrypted payload to be interpreted as MIME.
    msg = RMail::Parser.read output
    if msg.header.content_type =~ %r{^multipart/} && !msg.multipart?
      output = "MIME-Version: 1.0\n" + output
      output.force_encoding Encoding::ASCII_8BIT if output.respond_to? :force_encoding
      msg = RMail::Parser.read output
    end
    notice = Chunk::CryptoNotice.new :valid, "This message has been decrypted for display"
    [notice, sig, msg]
  end

private

  def unknown_status lines=[]
    Chunk::CryptoNotice.new :unknown, "Unable to determine validity of cryptographic signature", lines
  end

  def cant_find_binary
    ["Can't find gpg binary in path."]
  end

  ## here's where we munge rmail output into the format that signed/encrypted
  ## PGP/GPG messages should be
  def format_payload payload
    payload.to_s.gsub(/(^|[^\r])\n/, "\\1\r\n").gsub(/^MIME-Version: .*\r\n/, "")
  end

  def run_gpg args, opts={}
    args = HookManager.run("gpg-args", { :args => args }) || args
    cmd = "#{@cmd} #{args}"
    if opts[:interactive] && BufferManager.instantiated?
      output_fn = Tempfile.new "redwood.output"
      output_fn.close
      cmd += " > #{output_fn.path} 2> /dev/null"
      debug "crypto: running: #{cmd}"
      BufferManager.shell_out cmd
      IO.read(output_fn.path) rescue "can't read output"
    else
      debug "crypto: running: #{cmd}"
      `#{cmd} 2> /dev/null`
    end
  end
end
end
