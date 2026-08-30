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

/-! ## The trust store

Where the certificates for verifying an origin come from.

`SSL_CTX_set_default_verify_paths` looks in the directory OpenSSL was compiled
with, which is only the right place when the library was built where it runs.
A statically linked OpenSSL from a package manager's store carries that store's
path, which does not exist on the machine — and the call still reports success,
so the failure surfaces as an unverifiable certificate on the first request.

So the location is probed here instead, in Lean, where the list can be read.
`$SSL_CERT_FILE` is deliberately *not* consulted: `auth setup` exports it
pointing at this proxy's own CA, and a daemon started from such a shell would
then trust only itself. -/

/-- Where distributions keep the system bundle, in the order they are tried. -/
def trustStoreCandidates : List String :=
  [ "/etc/ssl/certs/ca-certificates.crt",     -- Debian, Ubuntu, Arch, Alpine
    "/etc/pki/tls/certs/ca-bundle.crt",       -- Fedora, RHEL
    "/etc/ssl/ca-bundle.pem",                 -- openSUSE
    "/etc/ssl/cert.pem",                      -- macOS ports, some BSDs
    "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem" ]

/-- The trust store to verify origins against.

An explicit setting wins.  Otherwise the first candidate that exists is used,
and failing that the empty string, which leaves OpenSSL to its compiled-in
defaults — right when the library was built where it runs, and checked for
emptiness at startup either way. -/
def resolveTrustStore (configured : String) : IO String := do
  if !configured.isEmpty then return configured
  for candidate in trustStoreCandidates do
    if ← System.FilePath.pathExists candidate then return candidate
  return ""

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
