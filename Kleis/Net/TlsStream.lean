import Kleis.Net.Tls
import Kleis.Net.Stream

/-!
# TLS as a stream

Wrapping a `Stream` in a TLS session, in both directions.

All the work is pumping: the session is a byte transform with two sides, and
this drives it — take ciphertext it wants sent and write it to the transport,
read ciphertext from the transport and feed it in, until the handshake finishes
or the peer goes away.

Because the session never sees the transport, the same code wraps a TCP
connection, a unix socket, or a pair of in-memory buffers in a test.
-/

namespace Kleis
namespace Net

open LeanBiscuit (Bytes)

/-- Write out whatever the session wants to send. -/
private def flushOut (inner : Stream) (s : Tls.Session) : IO Unit := do
  let rec go (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      let out ← Tls.pull s
      if out.size == 0 then pure ()
      else do
        inner.write out
        go fuel
  go 64

/-- Drive a handshake to completion. -/
private def runHandshake (inner : Stream) (s : Tls.Session) (what : String) : IO Unit := do
  let rec go (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => throw (IO.userError s!"the {what} TLS handshake did not finish")
    | fuel + 1 =>
      let progress ← Tls.handshake s
      flushOut inner s
      match progress with
      | .done => pure ()
      | .failed => throw (IO.userError s!"the {what} TLS handshake failed: {← Tls.lastError s}")
      | .wantMore => do
        let chunk ← inner.read 16384
        if chunk.size == 0 then
          throw (IO.userError s!"the peer closed the connection during the {what} handshake")
        Tls.feed s chunk
        go fuel
  go 256

/-- Wrap an established session as a stream. -/
private def sessionStream (inner : Stream) (s : Tls.Session) (describe : String) : Stream where
  read := fun max => do
    let rec go (fuel : Nat) : IO Bytes := do
      match fuel with
      | 0 => return ByteArray.empty
      | fuel + 1 =>
        let plain ← Tls.readRaw s (UInt32.ofNat (max.max 1))
        if plain.size > 0 then return plain
        if ← Tls.atEof s then return ByteArray.empty
        let chunk ← inner.read 16384
        if chunk.size == 0 then return ByteArray.empty
        Tls.feed s chunk
        flushOut inner s
        go fuel
    go 256
  write := fun b => do
    let rec pump (off : Nat) (fuel : Nat) : IO Unit := do
      if off ≥ b.size then pure () else
      match fuel with
      | 0 => throw (IO.userError "the TLS session stopped accepting data")
      | fuel + 1 =>
        let n ← Tls.writeRaw s (Bytes.drop b off)
        flushOut inner s
        if n == 0 then do
          -- The session wants to read before it can write again: a
          -- renegotiation or a post-handshake message.
          let chunk ← inner.read 16384
          if chunk.size == 0 then throw (IO.userError "the peer closed the connection")
          Tls.feed s chunk
          pump off fuel
        else pump (off + n.toNat) fuel
    pump 0 1024
  close := do
    try Tls.close s; flushOut inner s catch _ => pure ()
    inner.close
  describe

/-- Speak TLS to a server over an existing transport, verifying its certificate
against `hostname`. -/
def tlsClient (ctx : Tls.Context) (inner : Stream) (hostname : String) : IO Stream := do
  let s ← Tls.mkSession ctx false hostname
  runHandshake inner s s!"client to {hostname}"
  return sessionStream inner s s!"tls client {hostname} ({← Tls.version s})"

/-- Accept TLS from a client over an existing transport.

`replay` is the ClientHello the caller already read in order to find the SNI;
it is fed to the session before the handshake starts, so the peek costs no
bytes. -/
def tlsServer (ctx : Tls.Context) (inner : Stream) (replay : Bytes) : IO Stream := do
  let s ← Tls.mkSession ctx true ""
  if replay.size > 0 then Tls.feed s replay
  runHandshake inner s "server"
  return sessionStream inner s s!"tls server ({← Tls.version s})"

end Net
end Kleis
