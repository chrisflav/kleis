import LeanBiscuit

/-!
# Standard base64

`LeanBiscuit.Base64` is the URL-safe alphabet, which is what biscuit tokens
use.  HTTP basic authentication and PEM want the standard alphabet with `+`,
`/` and `=` padding, so that is here.
-/

namespace Auth
namespace Base64

open LeanBiscuit (Bytes)

/-- The standard alphabet. -/
def alphabet : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

/-- Encode, with `=` padding. -/
def encode (b : Bytes) : String :=
  let chars := alphabet.toList.toArray
  let rec go (i : Nat) (acc : List Char) (fuel : Nat) : List Char :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if i ≥ b.size then acc
      else
        let b0 := (b[i]!).toNat
        let has1 := i + 1 < b.size
        let has2 := i + 2 < b.size
        let b1 := if has1 then (b[i + 1]!).toNat else 0
        let b2 := if has2 then (b[i + 2]!).toNat else 0
        let n := b0 * 65536 + b1 * 256 + b2
        let c0 := chars[n / 262144]!
        let c1 := chars[(n / 4096) % 64]!
        let c2 := if has1 then chars[(n / 64) % 64]! else '='
        let c3 := if has2 then chars[n % 64]! else '='
        go (i + 3) (acc ++ [c0, c1, c2, c3]) fuel
  String.ofList (go 0 [] (b.size + 1))

/-- The value of one alphabet character. -/
private def valueOf? (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- Decode, tolerating missing padding and whitespace. -/
def decode? (s : String) : Option Bytes := do
  let digits := s.toList.filter fun c => c != '=' && c != '\n' && c != '\r' && c != ' '
  let vals ← digits.mapM valueOf?
  let rec go (l : List Nat) (acc : List UInt8) (fuel : Nat) : Option (List UInt8) :=
    match fuel with
    | 0 => some acc
    | fuel + 1 =>
      match l with
      | [] => some acc
      | [_] => none
      | [a, b] => some (acc ++ [UInt8.ofNat ((a * 4 + b / 16) % 256)])
      | [a, b, c] =>
        some (acc ++ [UInt8.ofNat ((a * 4 + b / 16) % 256),
                      UInt8.ofNat ((b * 16 + c / 4) % 256)])
      | a :: b :: c :: d :: rest =>
        go rest (acc ++ [UInt8.ofNat ((a * 4 + b / 16) % 256),
                         UInt8.ofNat ((b * 16 + c / 4) % 256),
                         UInt8.ofNat ((c * 64 + d) % 256)]) fuel
  let bytes ← go vals [] (vals.length + 1)
  pure ⟨bytes.toArray⟩

end Base64
end Auth
