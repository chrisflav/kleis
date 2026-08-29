import Auth.Ca.Der
import LeanBiscuit

/-!
# X.509

Building and signing certificates, over secp256r1 with SHA-256.

The keys and the signature come from `lean-biscuit`, which already implements
the curve for biscuit's own signatures.  So the certificate path is written in
the same library, and against the same arithmetic, as the token path — nothing
here trusts the FFI, which only ever *reads* what this produces.

Only the profile a local intercepting CA needs is here: a root that signs, and
leaves that authenticate a host.  There is no support for anything a public CA
would do, deliberately.
-/

namespace Auth
namespace X509

open LeanBiscuit
open LeanBiscuit (Bytes)

/-! ## Object identifiers -/

/-- `ecdsa-with-SHA256`. -/
def oidEcdsaSha256 : String := "1.2.840.10045.4.3.2"
/-- `id-ecPublicKey`. -/
def oidEcPublicKey : String := "1.2.840.10045.2.1"
/-- `prime256v1`, the curve secp256r1. -/
def oidPrime256v1 : String := "1.2.840.10045.3.1.7"
/-- `id-at-commonName`. -/
def oidCommonName : String := "2.5.4.3"
/-- `id-at-organizationName`. -/
def oidOrganization : String := "2.5.4.10"
/-- `id-ce-subjectKeyIdentifier`. -/
def oidSubjectKeyId : String := "2.5.29.14"
/-- `id-ce-keyUsage`. -/
def oidKeyUsage : String := "2.5.29.15"
/-- `id-ce-subjectAltName`. -/
def oidSubjectAltName : String := "2.5.29.17"
/-- `id-ce-basicConstraints`. -/
def oidBasicConstraints : String := "2.5.29.19"
/-- `id-ce-authorityKeyIdentifier`. -/
def oidAuthorityKeyId : String := "2.5.29.35"
/-- `id-ce-extKeyUsage`. -/
def oidExtKeyUsage : String := "2.5.29.37"
/-- `id-kp-serverAuth`. -/
def oidServerAuth : String := "1.3.6.1.5.5.7.3.1"

/-! ## Pieces -/

/-- The affine coordinates of a curve point. -/
private def affine (P : P256.Point) : Option (Nat × Nat) :=
  if P.Z == 0 then none
  else
    let zi := P256.F.inv P.Z
    let zi2 := P256.F.mul zi zi
    some (P256.F.mul P.X zi2, P256.F.mul P.Y (P256.F.mul zi2 zi))

/-- The uncompressed SEC1 encoding of a public key, `04 ‖ X ‖ Y`.

Uncompressed rather than compressed: both are legal in a certificate, and every
verifier accepts the uncompressed form, which is not quite true the other
way round on older stacks. -/
def uncompressedPoint (secret : Bytes) : Option Bytes := do
  if secret.size != 32 then none else
  let d := Bytes.toNatBE secret
  if d == 0 || d ≥ P256.n then none else
  let (x, y) ← affine (P256.Point.smul d P256.Point.base)
  some (Bytes.ofList [0x04] ++ Bytes.ofNatBE 32 x ++ Bytes.ofNatBE 32 y)

/-- `AlgorithmIdentifier` for ECDSA with SHA-256. -/
def algorithmEcdsaSha256 : Bytes := Der.seq [Der.oid oidEcdsaSha256]

/-- `SubjectPublicKeyInfo` for a P-256 key. -/
def spki (publicPoint : Bytes) : Bytes :=
  Der.seq [Der.seq [Der.oid oidEcPublicKey, Der.oid oidPrime256v1],
           Der.bitString publicPoint]

/-- A `Name` with one common name, and optionally an organization. -/
def name (commonName : String) (organization : Option String := none) : Bytes :=
  let rdn (oid value : String) := Der.set [Der.seq [Der.oid oid, Der.utf8String value]]
  match organization with
  | some o => Der.seq [rdn oidOrganization o, rdn oidCommonName commonName]
  | none => Der.seq [rdn oidCommonName commonName]

/-- Two digits, zero padded. -/
private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

/-- A `UTCTime`, which is what a certificate valid before 2050 uses.

Past 2050 the encoding has to change to `GeneralizedTime`, so that is what
happens: the choice is made from the year rather than fixed, and a certificate
minted in 2051 is still well formed. -/
def time (seconds : Nat) : Bytes :=
  let days := (Int.ofNat seconds) / 86400
  let rem := seconds % 86400
  let (y, m, d) := Time.civilFromDays days
  let text := s!"{pad2 m}{pad2 d}{pad2 (rem / 3600)}{pad2 ((rem % 3600) / 60)}{pad2 (rem % 60)}Z"
  if y ≥ 1950 && y < 2050 then
    Der.tagged 0x17 (Bytes.ofString (pad2 (y.toNat % 100) ++ text))
  else
    Der.tagged 0x18 (Bytes.ofString (toString y ++ text))

/-- `Validity`. -/
def validity (notBefore notAfter : Nat) : Bytes := Der.seq [time notBefore, time notAfter]

/-- One extension. -/
def extension (oid : String) (critical : Bool) (value : Bytes) : Bytes :=
  if critical then Der.seq [Der.oid oid, Der.bool true, Der.octetString value]
  else Der.seq [Der.oid oid, Der.octetString value]

/-- `basicConstraints`, critical, as RFC 5280 requires for a CA. -/
def basicConstraints (isCa : Bool) : Bytes :=
  extension oidBasicConstraints true (if isCa then Der.seq [Der.bool true] else Der.seq [])

/-- `keyUsage`, critical.

For a CA: `keyCertSign` and `cRLSign`.  For a leaf: `digitalSignature` and
`keyAgreement`, which is what an ECDSA server certificate needs. -/
def keyUsage (isCa : Bool) : Bytes :=
  let bits : Bytes :=
    if isCa then ⟨#[1, 0x06]⟩   -- 6 unused bits, keyCertSign ‖ cRLSign
    else ⟨#[3, 0x88]⟩           -- 3 unused bits, digitalSignature ‖ keyAgreement
  extension oidKeyUsage true (Der.tagged 0x03 bits)

/-- `extKeyUsage` naming server authentication. -/
def extKeyUsageServer : Bytes :=
  extension oidExtKeyUsage false (Der.seq [Der.oid oidServerAuth])

/-- Parse a dotted-quad, for deciding whether a SAN entry is a name or an
address. -/
private def ipv4Bytes? (s : String) : Option Bytes := do
  let parts := s.splitOn "."
  if parts.length != 4 then none else
    let octets ← parts.mapM fun p => do
      let n ← p.toNat?
      if n > 255 then none else some (UInt8.ofNat n)
    some ⟨octets.toArray⟩

/-- `subjectAltName`.

A certificate's identity is its SAN, not its common name — every verifier has
ignored the common name for a decade — so this is the extension that decides
whether interception works. -/
def subjectAltName (names : List String) : Bytes :=
  extension oidSubjectAltName false (Der.seq (names.map fun n =>
    match ipv4Bytes? n with
    | some b => Der.implicit 7 b
    | none => Der.implicit 2 (Bytes.ofString n)))

/-- A key identifier: the SHA-256 of the public point, truncated to twenty
bytes.

RFC 5280 suggests SHA-1 and permits any other method.  SHA-1 is not in
`lean-biscuit` and would not be worth adding for this: the identifier links a
certificate to its issuer's key and is not a security boundary. -/
def keyIdentifier (publicPoint : Bytes) : Bytes :=
  Bytes.take (Sha256.hash publicPoint) 20

/-- `subjectKeyIdentifier`. -/
def subjectKeyId (publicPoint : Bytes) : Bytes :=
  extension oidSubjectKeyId false (Der.octetString (keyIdentifier publicPoint))

/-- `authorityKeyIdentifier`, naming the issuer's key. -/
def authorityKeyId (issuerPoint : Bytes) : Bytes :=
  extension oidAuthorityKeyId false
    (Der.seq [Der.implicit 0 (keyIdentifier issuerPoint)])

/-! ## Certificates -/

/-- What a certificate is being asked to say. -/
structure Spec where
  /-- The serial number.  Must be unique per issuer and unpredictable, so it is
  taken from the system entropy source rather than a counter. -/
  serial : Nat
  /-- The subject's common name. -/
  commonName : String
  /-- The organization, if any. -/
  organization : Option String := none
  /-- The DNS names and addresses this certificate is for. -/
  altNames : List String := []
  /-- Valid from, seconds since the epoch. -/
  notBefore : Nat
  /-- Valid until. -/
  notAfter : Nat
  /-- Whether this is a certificate authority. -/
  isCa : Bool := false

/-- The `TBSCertificate`: everything that is signed. -/
def tbs (spec : Spec) (subjectPoint issuerPoint : Bytes) (issuerName : Bytes) : Bytes :=
  let extensions :=
    [basicConstraints spec.isCa, keyUsage spec.isCa, subjectKeyId subjectPoint,
     authorityKeyId issuerPoint]
    ++ (if spec.isCa then [] else [extKeyUsageServer])
    ++ (if spec.altNames.isEmpty then [] else [subjectAltName spec.altNames])
  Der.seq [
    Der.explicit 0 (Der.integer 2),          -- version v3
    Der.integer spec.serial,
    algorithmEcdsaSha256,
    issuerName,
    validity spec.notBefore spec.notAfter,
    name spec.commonName spec.organization,
    spki subjectPoint,
    Der.explicit 3 (Der.seq extensions)]

/-- Build and sign a certificate.

`issuerSecret` signs; `subjectPoint` is the key being certified.  For a
self-signed root the two keys are the same, which is exactly what makes a root
a root. -/
def certificate (spec : Spec) (subjectPoint issuerSecret : Bytes)
    (issuerName : Option Bytes := none) : Except String Bytes := do
  let some issuerPoint := uncompressedPoint issuerSecret
    | throw "the issuer's private key is not a valid secp256r1 scalar"
  let issuerName := issuerName.getD (name spec.commonName spec.organization)
  let body := tbs spec subjectPoint issuerPoint issuerName
  let some signature := P256.sign issuerSecret body
    | throw "the certificate could not be signed"
  pure (Der.seq [body, algorithmEcdsaSha256, Der.bitString signature])

/-- A PKCS#8 `PrivateKeyInfo` for a P-256 secret, which is the form OpenSSL
reads from a `PRIVATE KEY` block. -/
def privateKeyInfo (secret : Bytes) : Except String Bytes := do
  let some point := uncompressedPoint secret
    | throw "the private key is not a valid secp256r1 scalar"
  let ecPrivateKey := Der.seq [
    Der.integer 1,
    Der.octetString secret,
    Der.explicit 1 (Der.bitString point)]
  pure (Der.seq [
    Der.integer 0,
    Der.seq [Der.oid oidEcPublicKey, Der.oid oidPrime256v1],
    Der.octetString ecPrivateKey])

/-- A certificate as PEM. -/
def certificatePem (der : Bytes) : String := Der.pem "CERTIFICATE" der

/-- A private key as PEM. -/
def privateKeyPem (secret : Bytes) : Except String String := do
  pure (Der.pem "PRIVATE KEY" (← privateKeyInfo secret))

end X509
end Auth
