import Auth.Util.Bytes

/-!
# Poly1305

RFC 8439 §2.5.  The one-time authenticator that makes the credential store
tamper-evident rather than merely unreadable.

The field arithmetic is done in `Nat`.  A hand-rolled 130 bit representation
would be faster and would be the place a subtle carry bug lived; `Nat` is
arbitrary precision, so the modular reduction is the definition rather than an
implementation of it.
-/

namespace Auth
namespace Poly1305

open LeanBiscuit (Bytes)

/-- The prime `2^130 - 5`. -/
def p : Nat := 1361129467683753853853498429727072845819

/-- Read a little-endian number from bytes. -/
def leNat (b : Bytes) : Nat :=
  b.toList.reverse.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Clamp `r` as the specification requires: the top four bits of each of four
bytes are cleared, and the bottom two bits of three others. -/
def clamp (r : Nat) : Nat :=
  r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- The tag of a message under a 32 byte key. -/
def mac (key message : Bytes) : Bytes := Id.run do
  let r := clamp (leNat (Bytes.take key 16))
  let s := leNat (Bytes.slice key 16 32)
  let mut acc : Nat := 0
  let blocks := (message.size + 15) / 16
  for i in [0:blocks] do
    let chunk := Bytes.slice message (i * 16) (i * 16 + 16)
    -- Each block is read as a little-endian number with a 1 bit appended
    -- above its highest byte, which is what distinguishes a short final block
    -- from a full one padded with zeros.
    let n := leNat chunk + 2 ^ (8 * chunk.size)
    acc := ((acc + n) * r) % p
  let total := (acc + s) % (2 ^ 128)
  return ⟨(((List.range 16).map fun i => UInt8.ofNat ((total >>> (8 * i)) % 256))).toArray⟩

/-- Compare two tags without an early exit.

A verifier that returns as soon as two bytes differ tells an attacker how many
leading bytes of a guessed tag were right, which is enough to forge one byte at
a time. -/
def constantTimeEq (a b : Bytes) : Bool := Id.run do
  if a.size != b.size then return false
  let mut diff : UInt8 := 0
  for i in [0:a.size] do
    diff := diff ||| (a[i]! ^^^ b[i]!)
  return diff == 0

end Poly1305
end Auth
