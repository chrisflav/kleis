import Auth.Util.Bytes

/-!
# Streams

The seam every transport goes through.  A stream reads bytes, writes bytes and
closes; a plain TCP connection is one, a TLS session over a TCP connection is
another, and a pair of buffers in a test is a third.

Everything above this line — the HTTP reader, the proxy session, the whole
policy pipeline — is written against this and can therefore be exercised
without a socket or a certificate anywhere in sight.

A record of functions rather than a class, because the set of transports is
small, closed, and chosen at runtime by configuration.
-/

namespace Auth
namespace Net

open LeanBiscuit (Bytes)

/-- A bidirectional byte stream. -/
structure Stream where
  /-- Read up to `max` bytes.  An empty result means end of stream. -/
  read : Nat → IO Bytes
  /-- Write everything given, or fail. -/
  write : Bytes → IO Unit
  /-- Release the underlying resources.  Idempotent. -/
  close : IO Unit
  /-- What this is, for logs. -/
  describe : String

/-- Read until `n` bytes have arrived or the stream ends. -/
partial def Stream.readExactly (s : Stream) (n : Nat) : IO Bytes := do
  let rec go (acc : Bytes) : IO Bytes := do
    if acc.size ≥ n then return acc
    let chunk ← s.read (n - acc.size)
    if chunk.size == 0 then return acc
    go (acc ++ chunk)
  go ByteArray.empty

/-- A stream over two byte buffers, for tests: what is written to one is read
from the other. -/
def Stream.ofBuffers (input : IO.Ref Bytes) (output : IO.Ref Bytes) : Stream where
  read := fun max => do
    let buf ← input.get
    let n := min max buf.size
    input.set (Bytes.drop buf n)
    return Bytes.take buf n
  write := fun b => output.modify (· ++ b)
  close := pure ()
  describe := "buffer"

end Net
end Auth
