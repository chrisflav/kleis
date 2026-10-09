import Kleis.Net.Resolve
import Kleis.Net.Stream
import Std.Internal.UV.TCP

/-!
# TCP

A `Stream` over a TCP connection, and the listener that produces them.

Connecting tries every address a name resolved to before giving up, which is
what makes the proxy work on a host whose IPv6 route is broken — the case that
otherwise shows up as an inexplicable hang on the first request.
-/

namespace Kleis
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
  -- Resolved by `close`.  A read waits on it as well as on the socket, so closing the
  -- stream wakes a read blocked in another task: neither `shutdown` nor `cancelRecv`
  -- does, and a tunnel whose origin never closed its side used to keep that task, its
  -- thread and both descriptors for good.
  let closedSignal ← IO.Promise.new (α := Unit)
  return {
    read := fun max => do
      if ← closed.get then return ByteArray.empty
      let received ← sock.recv? (UInt64.ofNat (max.max 1))
      let first ← IO.waitAny [received.result!.map some, closedSignal.result!.map fun _ => none]
      match first with
      | none => return ByteArray.empty
      | some (.error e) => throw e
      | some (.ok none) => return ByteArray.empty
      | some (.ok (some b)) => return b
    write := fun b => do
      if b.size == 0 then pure () else await (← sock.send #[b])
    close := do
      if !(← closed.get) then
        closed.set true
        closedSignal.resolve ()
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

/-- Whether an IPv4 address, by its first two octets, is internal; see `isInternal`. -/
def isInternalV4 (b0 b1 : Nat) : Bool :=
    b0 == 0 || b0 == 10 || b0 == 127 || (b0 == 169 && b1 == 254)
      || (b0 == 172 && 16 ≤ b1 && b1 ≤ 31) || (b0 == 192 && b1 == 168)
      || (b0 == 100 && 64 ≤ b1 && b1 ≤ 127) || b0 ≥ 224

/-- Is an address one only this host or its own network should reach — loopback,
private, link-local, carrier-grade NAT, unspecified, multicast, unique-local, or
an IPv4 address mapped into IPv6 that is one of those?  What a blind tunnel must
not be let at by default: the daemon's own host, a cloud metadata service, the
deployment's internal network. -/
def isInternal : Std.Net.SocketAddress → Bool
  | .v4 a => isInternalV4 a.addr.octets[0].toNat a.addr.octets[1].toNat
  | .v6 a =>
    let s := a.addr.segments
    let first := s[0].toNat
    let allZeroUpTo (n : Nat) := (List.range n).all fun i => (s[i]?.map (·.toNat)).getD 0 == 0
    -- ::, ::1
    (allZeroUpTo 7 && s[7].toNat ≤ 1)
      -- fc00::/7, fe80::/10, ff00::/8
      || (first &&& 0xfe00) == 0xfc00 || (first &&& 0xffc0) == 0xfe80 || (first &&& 0xff00) == 0xff00
      -- ::ffff:a.b.c.d, judged as the IPv4 address it is
      || (allZeroUpTo 5 && s[5].toNat == 0xffff && isInternalV4 (s[6].toNat / 256) (s[6].toNat % 256))

/-- Connect to a host, but only to the addresses `allow` accepts.

The check and the connection are on the same resolved addresses: resolving once
to check and letting `connect` resolve again would let a name that answers
differently the second time — DNS rebinding — through the check. -/
def connectChecked (host : String) (port : UInt16) (allow : Std.Net.SocketAddress → Bool) :
    IO Stream := do
  let addrs ← resolve host port
  let allowed := addrs.filter allow
  if allowed.isEmpty && !addrs.isEmpty then
    throw (IO.userError s!"`{host}` resolves only to addresses this proxy does not tunnel to")
  let mut lastError : Option IO.Error := none
  for addr in allowed do
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
end Kleis
