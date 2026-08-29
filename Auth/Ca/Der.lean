import Auth.Util.Bytes
import Auth.Util.Base64

/-!
# DER

Just enough Distinguished Encoding Rules to write an X.509 certificate: the
tags, the length form, and the handful of universal types a certificate uses.

Writing rather than reading.  The proxy mints certificates and never has to
parse one — OpenSSL does that on the other side of the FFI — so this is an
encoder, and an encoder is the half of ASN.1 that can be got right by
construction: every value carries its own tag and length, and nothing here
takes untrusted input.
-/

namespace Auth
namespace Der

open LeanBiscuit (Bytes)

/-- The definite length form: short for under 128, otherwise a count of
length bytes with the high bit set. -/
def length (n : Nat) : Bytes :=
  if n < 128 then ⟨#[UInt8.ofNat n]⟩
  else
    let rec bytes (n : Nat) (acc : List UInt8) : List UInt8 :=
      if h : n = 0 then acc else bytes (n / 256) (UInt8.ofNat (n % 256) :: acc)
    termination_by n
    decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
    let bs := bytes n []
    ⟨(UInt8.ofNat (0x80 + bs.length) :: bs).toArray⟩

/-- A tag, a length and a body. -/
def tagged (tag : UInt8) (body : Bytes) : Bytes :=
  ⟨#[tag]⟩ ++ length body.size ++ body

/-- `SEQUENCE`. -/
def seq (items : List Bytes) : Bytes := tagged 0x30 (items.foldl (· ++ ·) ByteArray.empty)

/-- `SET`. -/
def set (items : List Bytes) : Bytes := tagged 0x31 (items.foldl (· ++ ·) ByteArray.empty)

/-- `INTEGER`, from a natural number.

A leading zero byte is prepended when the top bit is set, because DER integers
are signed and a certificate serial that looked negative would be rejected. -/
def integer (n : Nat) : Bytes :=
  let rec bytes (n : Nat) (acc : List UInt8) : List UInt8 :=
    if h : n = 0 then acc else bytes (n / 256) (UInt8.ofNat (n % 256) :: acc)
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
  let bs := match bytes n [] with
    | [] => [0]
    | l => if l.headD 0 ≥ 0x80 then 0 :: l else l
  tagged 0x02 ⟨bs.toArray⟩

/-- `INTEGER`, from big-endian bytes that are already the value. -/
def integerOfBytes (b : Bytes) : Bytes :=
  let l := b.toList.dropWhile (· == 0)
  let l := match l with
    | [] => [0]
    | _ => if l.headD 0 ≥ 0x80 then 0 :: l else l
  tagged 0x02 ⟨l.toArray⟩

/-- `BOOLEAN`.  DER requires `0xff` for true, not merely a non-zero byte. -/
def bool (b : Bool) : Bytes := tagged 0x01 ⟨#[if b then 0xff else 0x00]⟩

/-- `NULL`. -/
def null : Bytes := ⟨#[0x05, 0x00]⟩

/-- `OCTET STRING`. -/
def octetString (b : Bytes) : Bytes := tagged 0x04 b

/-- `BIT STRING` with no unused trailing bits. -/
def bitString (b : Bytes) : Bytes := tagged 0x03 (⟨#[0]⟩ ++ b)

/-- `UTF8String`. -/
def utf8String (s : String) : Bytes := tagged 0x0c (Bytes.ofString s)

/-- `IA5String`. -/
def ia5String (s : String) : Bytes := tagged 0x16 (Bytes.ofString s)

/-- `OBJECT IDENTIFIER`, from its dotted form.

The first two arcs share a byte as `40*a + b`; the rest are base-128 with a
continuation bit.  A malformed OID here is a programming error, not input, so
an unparseable one encodes as empty rather than propagating a failure through
every call site. -/
def oid (dotted : String) : Bytes :=
  let arcs := (dotted.splitOn ".").filterMap (·.toNat?)
  match arcs with
  | a :: b :: rest =>
    let base128 (n : Nat) : List UInt8 :=
      if n == 0 then [0]
      else
        let rec go (n : Nat) (acc : List UInt8) : List UInt8 :=
          if h : n = 0 then acc
          else go (n / 128) (UInt8.ofNat (n % 128) :: acc)
        termination_by n
        decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)
        match go n [] with
        | [] => [0]
        | l => (l.dropLast.map fun x => x ||| 0x80) ++ [l.getLastD 0]
    tagged 0x06 ⟨((UInt8.ofNat (40 * a + b) :: rest.flatMap base128)).toArray⟩
  | _ => tagged 0x06 ByteArray.empty

/-- A context-specific constructed tag, `[n] EXPLICIT`. -/
def explicit (n : UInt8) (body : Bytes) : Bytes := tagged (0xa0 ||| n) body

/-- A context-specific primitive tag, `[n] IMPLICIT`. -/
def implicit (n : UInt8) (body : Bytes) : Bytes := tagged (0x80 ||| n) body

/-- Wrap DER in a PEM block. -/
def pem (label : String) (body : Bytes) : String :=
  let b64 := Base64.encode body
  let rec wrap (s : List Char) (acc : List String) (fuel : Nat) : List String :=
    match fuel, s with
    | _, [] => acc.reverse
    | 0, _ => acc.reverse
    | fuel + 1, _ => wrap (s.drop 64) (String.ofList (s.take 64) :: acc) fuel
  let lines := wrap b64.toList [] (b64.length + 1)
  s!"-----BEGIN {label}-----\n" ++ String.join (lines.map (· ++ "\n")) ++
    s!"-----END {label}-----\n"

end Der
end Auth
