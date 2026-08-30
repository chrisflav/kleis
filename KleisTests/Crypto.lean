import KleisTests.Harness

/-! # Cryptography, against the vectors of RFC 8439 and RFC 7914 -/

namespace KleisTests

open Kleis LeanBiscuit

private def hexb (s : String) : Bytes := (Bytes.ofHex? s).getD ByteArray.empty

def cryptoTests : IO Unit := do
  group "chacha20 / poly1305 (RFC 8439)"
  let key := hexb "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  let nonce := hexb "000000090000004a00000000"
  checkEq "block function"
    (Bytes.toHex (ChaCha20.block key 1 nonce))
    ("10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e"
      ++ "d2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e")
  checkEq "poly1305"
    (Bytes.toHex (Poly1305.mac
      (hexb "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
      (Bytes.ofString "Cryptographic Forum Research Group")))
    "a8061dc1305136c6c22b8baf0c0127a9"

  let aeadKey := hexb "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let aeadNonce := hexb "070000004041424344454647"
  let aad := hexb "50515253c0c1c2c3c4c5c6c7"
  let plain := Bytes.ofString
    ("Ladies and Gentlemen of the class of '99: If I could offer you "
      ++ "only one tip for the future, sunscreen would be it.")
  let sealed := Aead.encrypt aeadKey aeadNonce aad plain
  checkEq "aead tag"
    (Bytes.toHex (Kleis.Bytes.drop sealed (sealed.size - 16)))
    "1ae10b594f09e26a7e902ecbd0600691"
  checkEq "aead round trip"
    ((Aead.decrypt? aeadKey aeadNonce aad sealed).map Kleis.Bytes.toStringLossy)
    (some (Kleis.Bytes.toStringLossy plain))
  let tampered := sealed.set! 3 (sealed[3]! ^^^ 1)
  check "a modified ciphertext is rejected"
    (Aead.decrypt? aeadKey aeadNonce aad tampered).isNone
  check "modified associated data is rejected"
    (Aead.decrypt? aeadKey aeadNonce (Bytes.ofString "other") sealed).isNone

  group "pbkdf2 (RFC 7914)"
  checkEq "one iteration"
    (Bytes.toHex (Aead.pbkdf2 (Bytes.ofString "passwd") (Bytes.ofString "salt") 1 32))
    "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc"

end KleisTests
