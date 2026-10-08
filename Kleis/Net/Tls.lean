import Kleis.Util.Bytes

/-!
# TLS

Bindings to the OpenSSL shim in `ffi/Tls.c`.  A session is a byte transform,
not a socket: ciphertext is fed in and drawn out, plaintext read and written,
and whatever carries the bytes is somebody else's problem.

This is the one part of the system that is not written in Lean, and the
interface is drawn so that it is the only part that has to be.  Everything
above `Kleis.Net.Stream` is testable over plain sockets, and a TLS
implementation in Lean — which `lean-biscuit` already has most of the
primitives for — would drop in here without a line changing anywhere else.
-/

namespace Kleis
namespace Net
namespace Tls

open LeanBiscuit (Bytes)

/-- An `SSL_CTX`: a certificate, a key and a trust configuration, shared by
every session that uses it. -/
opaque ContextPointed : NonemptyType
/-- A TLS context. -/
def Context : Type := ContextPointed.type
instance : Nonempty Context := ContextPointed.property

/-- An `SSL` session together with its two memory BIOs. -/
opaque SessionPointed : NonemptyType
/-- A TLS session. -/
def Session : Type := SessionPointed.type
instance : Nonempty Session := SessionPointed.property

/-- A client context.  Certificate verification is always on: the whole point
of this process is that it holds a credential, and a credential handed to an
unauthenticated peer is worse than no proxy at all.  An empty `caFile` means
the system trust store. -/
@[extern "kleis_tls_ctx_client"]
opaque mkClientContext (caFile : @& String) : IO Context

/-- A server context from a PEM chain and key held in memory — in memory
because a leaf here is minted per connection, and on disk it would be a
temporary file holding a private key. -/
@[extern "kleis_tls_ctx_server"]
opaque mkServerContext (certPem keyPem : @& String) : IO Context

/-- How many certificates a context trusts.

`SSL_CTX_set_default_verify_paths` reports success even when the directory it
was compiled to look in does not exist — which is what happens whenever the
OpenSSL that got linked was built somewhere other than where it runs, as a
statically linked one from a package manager's store generally is.  The context
then trusts nothing, and the symptom is a certificate verification failure on
the first upstream request rather than anything about trust stores. -/
@[extern "kleis_tls_ctx_size"]
opaque contextSize (ctx : @& Context) : IO Nat

/-- A new session.  `hostname` is the SNI to send and the name to verify for a
client, and is ignored for a server. -/
@[extern "kleis_tls_conn_new"]
opaque mkSession (ctx : @& Context) (isServer : Bool) (hostname : @& String) : IO Session

/-- Hand the session ciphertext that arrived from the peer. -/
@[extern "kleis_tls_feed"]
opaque feed (s : @& Session) (ciphertext : @& ByteArray) : IO Unit

/-- Take ciphertext the session wants sent to the peer. -/
@[extern "kleis_tls_pull"]
opaque pull (s : @& Session) : IO ByteArray

/-- Advance the handshake. -/
@[extern "kleis_tls_handshake"]
opaque handshakeStep (s : @& Session) : IO UInt8

/-- Encrypt plaintext, returning how much was accepted. -/
@[extern "kleis_tls_write"]
opaque writeRaw (s : @& Session) (plaintext : @& ByteArray) : IO UInt32

/-- Decrypt what is available, up to `max` bytes.  Empty means nothing is
ready, which is not the same as end of stream — see `atEof`. -/
@[extern "kleis_tls_read"]
opaque readRaw (s : @& Session) (max : UInt32) : IO ByteArray

/-- Has the peer sent `close_notify`? -/
@[extern "kleis_tls_eof"]
opaque atEof (s : @& Session) : IO Bool

/-- Begin an orderly close. -/
@[extern "kleis_tls_close"]
opaque close (s : @& Session) : IO Unit

/-- The last handshake failure. -/
@[extern "kleis_tls_error"]
opaque lastError (s : @& Session) : IO String

/-- The negotiated protocol version, for the audit record. -/
@[extern "kleis_tls_version"]
opaque version (s : @& Session) : IO String

/-- Sign a message with RS256 under a PEM private key: what a GitHub App signs
the token it exchanges for an installation token with.  The key is parsed and
freed within the call. -/
@[extern "kleis_sign_rs256"]
opaque signRs256 (keyPem : @& ByteArray) (message : @& ByteArray) : IO ByteArray

/-- How a handshake step ended. -/
inductive Progress where
  /-- The handshake is complete. -/
  | done
  /-- More input is needed from the peer. -/
  | wantMore
  /-- It failed. -/
  | failed
  deriving Repr, DecidableEq

/-- Advance the handshake, as a decision rather than a number. -/
def handshake (s : Session) : IO Progress := do
  match ← handshakeStep s with
  | 0 => return .done
  | 1 => return .wantMore
  | _ => return .failed

end Tls
end Net
end Kleis
