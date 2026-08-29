import Auth.Crypto.ChaCha20
import Auth.Crypto.Poly1305
import LeanBiscuit

/-!
# ChaCha20-Poly1305 and PBKDF2

RFC 8439 §2.8 for the AEAD, RFC 8018 for the key derivation.  Together they are
what stands between a stolen data directory and the credentials in it.

The AEAD is authenticated, not merely encrypting: a store whose ciphertext can
be altered without detection is a store where an attacker can change which host
a credential is bound to.  The associated data is where that binding goes.
-/

namespace Auth
namespace Aead

open LeanBiscuit

/-- Pad to a multiple of sixteen bytes with zeros. -/
private def pad16 (b : Bytes) : Bytes :=
  let r := b.size % 16
  if r == 0 then ByteArray.empty else ⟨(List.replicate (16 - r) (0 : UInt8)).toArray⟩

/-- An eight byte little-endian length. -/
private def len64 (n : Nat) : Bytes :=
  ⟨(((List.range 8).map fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))).toArray⟩

/-- The one-time Poly1305 key for a message: the first half of the keystream
block at counter zero. -/
private def polyKey (key nonce : Bytes) : Bytes :=
  Bytes.take (ChaCha20.block key 0 nonce) 32

/-- What the tag is computed over. -/
private def macData (aad ciphertext : Bytes) : Bytes :=
  aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext ++ len64 aad.size ++ len64 ciphertext.size

/-- Encrypt and authenticate.  Returns the ciphertext followed by its 16 byte
tag.

The key must be 32 bytes and the nonce 12, and a nonce must never be reused
with a key: ChaCha20 is a stream cipher, so two messages under one nonce differ
by the XOR of their plaintexts. -/
def encrypt (key nonce aad plaintext : Bytes) : Bytes :=
  let ciphertext := ChaCha20.apply key 1 nonce plaintext
  let tag := Poly1305.mac (polyKey key nonce) (macData aad ciphertext)
  ciphertext ++ tag

/-- Verify and decrypt.  `none` when the tag does not match, which is the only
answer a caller should get: a failed authentication says nothing about *why*. -/
def decrypt? (key nonce aad sealed : Bytes) : Option Bytes :=
  if sealed.size < 16 then none
  else
    let ciphertext := Bytes.take sealed (sealed.size - 16)
    let tag := Bytes.drop sealed (sealed.size - 16)
    let expected := Poly1305.mac (polyKey key nonce) (macData aad ciphertext)
    if Poly1305.constantTimeEq tag expected then
      some (ChaCha20.apply key 1 nonce ciphertext)
    else none

/-- One PBKDF2 block: `HMAC(password, salt ‖ i)` folded `iterations` times. -/
private def pbkdf2Block (password salt : Bytes) (iterations : Nat) (index : Nat) : Bytes :=
  Id.run do
    let counter : Bytes := ⟨#[UInt8.ofNat ((index >>> 24) % 256),
                             UInt8.ofNat ((index >>> 16) % 256),
                             UInt8.ofNat ((index >>> 8) % 256),
                             UInt8.ofNat (index % 256)]⟩
    let mut u := Hmac.sha256 password (salt ++ counter)
    let mut acc := u
    for _ in [1:iterations] do
      u := Hmac.sha256 password u
      acc := ⟨(List.range acc.size).map (fun i => acc[i]! ^^^ u[i]!) |>.toArray⟩
    return acc

/-- Derive `length` bytes from a passphrase, PBKDF2-HMAC-SHA256. -/
def pbkdf2 (password salt : Bytes) (iterations length : Nat) : Bytes := Id.run do
  let blocks := (length + 31) / 32
  let mut out : Bytes := ByteArray.empty
  for i in [1:blocks + 1] do
    out := out ++ pbkdf2Block password salt iterations i
  return Bytes.take out length

/-- The iteration count for a passphrase-derived store key.  High enough to
cost something on a stolen file, low enough that unlocking the daemon at
startup is not noticeable. -/
def defaultIterations : Nat := 600000

end Aead
end Auth
