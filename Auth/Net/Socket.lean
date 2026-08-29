import Auth.Net.Resolve
import Auth.Net.Stream
import Std.Internal.UV.TCP

/-!
# TCP

A `Stream` over a TCP connection, and the listener that produces them.

Connecting tries every address a name resolved to before giving up, which is
what makes the proxy work on a host whose IPv6 route is broken — the case that
otherwise shows up as an inexplicable hang on the first request.
-/

namespace Auth
namespace Net
namespace Tcp

open LeanBiscuit (Bytes)
open Std.Net
open Std.Internal.UV.TCP

/-- Wait for a promised result, re-raising whatever it holds. -/
private def await (p : IO.Promise (Except IO.Error α)) : IO α := do
  match ← IO.wait p.result! with
  | .error e => throw e
  | .ok v => pure v

/-- Wrap an open socket as a stream. -/
def ofSocket (sock : Socket) (describe : String) : IO Stream := do
  let closed ← IO.mkRef false
  return {
    read := fun max => do
      if ← closed.get then return ByteArray.empty
      match ← await (← sock.recv? (UInt64.ofNat (max.max 1))) with
      | none => return ByteArray.empty
      | some b => return b
    write := fun b => do
      if b.size == 0 then pure () else await (← sock.send #[b])
    close := do
      if !(← closed.get) then
        closed.set true
        try await (← sock.shutdown) catch _ => pure ()
    describe
  }

/-- Connect to a host and port, trying each resolved address in turn.

The error carries the last failure rather than the first: on a dual-stack host
the first attempt is usually the one that was never going to work, and
reporting it hides the reason the connection actually failed. -/
def connect (host : String) (port : UInt16) : IO Stream := do
  let addrs ← resolve host port
  let mut lastError : Option IO.Error := none
  for addr in addrs do
    try
      let sock ← Socket.new
      await (← sock.connect addr)
      return ← ofSocket sock s!"tcp {host}:{port}"
    catch e =>
      lastError := some e
  match lastError with
  | some e => throw e
  | none => throw (IO.userError s!"`{host}` resolved to no usable address")

/-- Bind and listen. -/
def listen (host : String) (port : UInt16) (backlog : Nat := 128) : IO (Socket × UInt16) := do
  let addrs ← resolve host port
  let addr := addrs[0]!
  let sock ← Socket.new
  sock.bind addr
  sock.listen (UInt32.ofNat backlog)
  let bound ← sock.getSockName
  let actual := match bound with
    | .v4 a => a.port
    | .v6 a => a.port
  return (sock, actual)

/-- Accept one connection. -/
def accept (server : Socket) : IO Stream := do
  let client ← await (← server.accept)
  let peer ← try
      let a ← client.getPeerName
      pure (match a with
        | .v4 x => toString x.addr
        | .v6 x => toString x.addr)
    catch _ => pure "unknown"
  ofSocket client peer

/-- The peer's address, for the `client_ip` fact. -/
def peerAddress (sock : Socket) : IO String := do
  try
    match ← sock.getPeerName with
    | .v4 a => return toString a.addr
    | .v6 a => return toString a.addr
  catch _ => return "unknown"

end Tcp
end Net
end Auth
