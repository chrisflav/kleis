import Auth.Util.Str
import Std.Net

/-!
# Name resolution

`getaddrinfo`, through the shim in `ffi/Net.c`, returning address literals.

Ordering, family preference and the connection attempt loop stay in Lean rather
than being buried in C: which address a proxy dials, and what it does when the
first one is unreachable, is behaviour worth being able to read.
-/

namespace Auth
namespace Net

/-- Every address a name resolves to, in the order the resolver returned them
— which on a dual-stack host is already sorted by RFC 6724. -/
@[extern "auth_net_resolve"]
opaque resolveRaw (host : @& String) : IO (Array String)

/-- Resolve a host to socket addresses on a port.

An address literal is passed through without asking the resolver, which
matters for a proxy: a client that dialled an address rather than a name has
already decided where it is going. -/
def resolve (host : String) (port : UInt16) : IO (Array Std.Net.SocketAddress) := do
  let literals ←
    if (Std.Net.IPv4Addr.ofString host).isSome || (Std.Net.IPv6Addr.ofString host).isSome
    then pure #[host]
    else resolveRaw host
  let mut out : Array Std.Net.SocketAddress := #[]
  for text in literals do
    if let some v4 := Std.Net.IPv4Addr.ofString text then
      out := out.push (.v4 { addr := v4, port })
    else if let some v6 := Std.Net.IPv6Addr.ofString text then
      out := out.push (.v6 { addr := v6, port })
  if out.isEmpty then
    throw (IO.userError s!"`{host}` resolved to no usable address")
  return out

end Net
end Auth
