import Kleis.Util.Bytes

/-!
# ChaCha20

RFC 8439 §2.  The stream cipher half of the authenticated encryption that
protects credentials at rest.

Written here rather than taken from OpenSSL for the same reason `lean-biscuit`
writes its own Ed25519: the credential store must not depend on the FFI that
exists only for TLS, and a daemon that cannot open its own store because a
shared library moved is a daemon that has locked the owner out of their
credentials.
-/

namespace Kleis
namespace ChaCha20

open LeanBiscuit (Bytes)

/-- The four constant words: `"expand 32-byte k"`, little-endian. -/
def constants : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Read a little-endian 32 bit word. -/
def word (b : Bytes) (off : Nat) : UInt32 :=
  let byte (i : Nat) : UInt32 := UInt32.ofNat (b[off + i]!).toNat
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24)

/-- Write a little-endian 32 bit word. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [UInt8.ofNat (w &&& 0xff).toNat,
   UInt8.ofNat ((w >>> 8) &&& 0xff).toNat,
   UInt8.ofNat ((w >>> 16) &&& 0xff).toNat,
   UInt8.ofNat ((w >>> 24) &&& 0xff).toNat]

/-- Rotate left. -/
def rotl (w : UInt32) (n : UInt32) : UInt32 := (w <<< n) ||| (w >>> (32 - n))

/-- One quarter round, on the state indices `a b c d`. -/
def quarterRound (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  let mut va := s[a]!; let mut vb := s[b]!; let mut vc := s[c]!; let mut vd := s[d]!
  va := va + vb; vd := rotl (vd ^^^ va) 16
  vc := vc + vd; vb := rotl (vb ^^^ vc) 12
  va := va + vb; vd := rotl (vd ^^^ va) 8
  vc := vc + vd; vb := rotl (vb ^^^ vc) 7
  s := s.set! a va; s := s.set! b vb; s := s.set! c vc; s := s.set! d vd
  return s

/-- One double round: four column rounds, then four diagonal rounds. -/
def doubleRound (s : Array UInt32) : Array UInt32 := Id.run do
  let mut s := s
  s := quarterRound s 0 4 8 12
  s := quarterRound s 1 5 9 13
  s := quarterRound s 2 6 10 14
  s := quarterRound s 3 7 11 15
  s := quarterRound s 0 5 10 15
  s := quarterRound s 1 6 11 12
  s := quarterRound s 2 7 8 13
  s := quarterRound s 3 4 9 14
  return s

/-- The initial state for a key, counter and nonce. -/
def state (key : Bytes) (counter : UInt32) (nonce : Bytes) : Array UInt32 :=
  constants
    ++ (Array.range 8).map (fun i => word key (i * 4))
    ++ #[counter]
    ++ (Array.range 3).map (fun i => word nonce (i * 4))

/-- One 64 byte keystream block. -/
def block (key : Bytes) (counter : UInt32) (nonce : Bytes) : Bytes := Id.run do
  let initial := state key counter nonce
  let mut s := initial
  for _ in [0:10] do
    s := doubleRound s
  let mut out : List UInt8 := []
  for i in [0:16] do
    out := out ++ wordBytes (s[i]! + initial[i]!)
  return ⟨out.toArray⟩

/-- Encrypt or decrypt: XOR the message with the keystream.

The operation is its own inverse, which is why one function serves both
directions and why a nonce must never be reused with a key. -/
def apply (key : Bytes) (counter : UInt32) (nonce : Bytes) (message : Bytes) : Bytes :=
  Id.run do
    let mut out : Array UInt8 := Array.emptyWithCapacity message.size
    let blocks := (message.size + 63) / 64
    for i in [0:blocks] do
      let ks := block key (counter + UInt32.ofNat i) nonce
      let start := i * 64
      let stop := min (start + 64) message.size
      for j in [start:stop] do
        out := out.push (message[j]! ^^^ ks[j - start]!)
    return ⟨out⟩

end ChaCha20
end Kleis
