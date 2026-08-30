import KleisTests.Harness

/-! # Certificates and TLS

These need the FFI, so they only run in the compiled test binary — the
interpreter cannot resolve statically linked symbols. -/

namespace KleisTests

open Kleis LeanBiscuit

/-- A private key from a fixed seed, so a failure is reproducible. -/
private def fixedSecret : Bytes := Bytes.ofList (List.replicate 32 (3 : UInt8))

def caTests : IO Unit := do
  group "DER"
  checkEq "short length" (Bytes.toHex (Der.length 5)) "05"
  checkEq "long length" (Bytes.toHex (Der.length 300)) "82012c"
  checkEq "an integer with the top bit set gets a leading zero"
    (Bytes.toHex (Der.integer 128)) "02020080"
  checkEq "a small integer does not" (Bytes.toHex (Der.integer 1)) "020101"
  checkEq "zero" (Bytes.toHex (Der.integer 0)) "020100"
  -- 1.2.840.10045.4.3.2, the OID every certificate here is signed under.
  checkEq "object identifier" (Bytes.toHex (Der.oid "1.2.840.10045.4.3.2"))
    "06082a8648ce3d040302"
  checkEq "boolean true is 0xff" (Bytes.toHex (Der.bool true)) "0101ff"

  group "X.509"
  match X509.uncompressedPoint fixedSecret with
  | none => check "a public point is computed" false
  | some point => do
    check "a public point is computed" true
    checkEq "uncompressed form" point.size 65
    checkEq "uncompressed tag" (point[0]!) 4
    let spec : X509.Spec := {
      serial := 12345, commonName := "example.test", organization := some "kleis"
      altNames := ["example.test", "127.0.0.1"]
      notBefore := 1700000000, notAfter := 1800000000, isCa := false }
    match X509.certificate spec point fixedSecret none with
    | .error e => check "a certificate is built and signed" false e
    | .ok der => do
      check "a certificate is built and signed" true
      -- The signature is over the TBS, so it must verify against the key.
      let body := X509.tbs spec point point (X509.name "example.test" (some "kleis"))
      check "the certificate is longer than what it signs" (der.size > body.size)
  match X509.privateKeyPem fixedSecret with
  | .error e => check "a private key renders as PEM" false e
  | .ok pem => do
    check "a private key renders as PEM" (pem.startsWith "-----BEGIN PRIVATE KEY-----")
    check "and ends properly" (pem.endsWith "-----END PRIVATE KEY-----\n")

  group "a certificate describes its own subject"
  -- The bug this guards: the issuer name used to be rebuilt from a constant
  -- rather than read from the CA certificate, so renaming the organisation --
  -- or loading a CA an older version wrote -- produced leaves whose issuer did
  -- not match any subject, and nothing could build a path to them.
  match X509.uncompressedPoint fixedSecret with
  | none => check "a point is computed" false
  | some point => do
    let name := X509.name "example CA" (some "someorg")
    let spec : X509.Spec := {
      serial := 7, commonName := "example CA", organization := some "someorg"
      notBefore := 1700000000, notAfter := 1800000000, isCa := true }
    match X509.certificate spec point fixedSecret none with
    | .error e => check "a CA certificate is built" false e
    | .ok der =>
      check "a CA certificate is built" true
      match X509.subjectOf? der with
      | none => check "its subject can be read back" false
      | some subject => do
        check "its subject can be read back" true
        -- Byte-identical, because that is what a verifier compares.
        checkEq "and is exactly what was encoded"
          (Bytes.toHex subject) (Bytes.toHex name)
    -- A certificate carrying a *different* name must read back that one, not
    -- whatever the program would construct today.
    let other : X509.Spec := { spec with commonName := "old name", organization := some "oldorg" }
    match X509.certificate other point fixedSecret none with
    | .error _ => check "a differently named CA is built" false
    | .ok der =>
      checkEq "the name read back follows the certificate, not the code"
        ((X509.subjectOf? der).map Bytes.toHex)
        (some (Bytes.toHex (X509.name "old name" (some "oldorg"))))

  group "the local CA (FFI)"
  let root ← Ca.loadOrCreateRoot
  check "a root exists" (root.der.size > 100)
  check "its PEM is a certificate" (root.pem.startsWith "-----BEGIN CERTIFICATE-----")
  let leaf ← root.mint "github.com"
  check "a leaf is minted" (leaf.certPem.startsWith "-----BEGIN CERTIFICATE-----")
  -- The chain is leaf then root, so a client that trusts the root can build a
  -- path without holding anything else.
  check "the chain carries the root too"
    ((leaf.certPem.splitOn "-----BEGIN CERTIFICATE-----").length == 3)
  -- OpenSSL reading them back is the real test of the encoder.
  let _ ← Net.Tls.mkServerContext leaf.certPem leaf.keyPem
  check "OpenSSL accepts the certificate and key together" true

def tlsTests : IO Unit := do
  group "TLS through the whole stack (FFI)"
  let root ← Ca.loadOrCreateRoot
  let cache ← Ca.Cache.create root
  let caFile := ((← Dirs.ca) / "ca.crt").toString
  Store.writePublic (System.FilePath.mk caFile) root.pem
  let (server, port) ← Net.Tcp.listen "127.0.0.1" 0

  let serverTask ← IO.asTask (prio := .dedicated) do
    let raw ← Net.Tcp.accept server
    let (hello, sni) ← Proxy.peekSni raw
    let ctx ← cache.contextFor (sni.getD "localhost")
    let tls ← Net.tlsServer ctx raw hello
    let request ← tls.read 4096
    tls.write (Bytes.ofString s!"echo:{Kleis.Bytes.toStringLossy request}")
    tls.close
    pure (sni.getD "")

  let clientCtx ← Net.Tls.mkClientContext caFile
  let raw ← Net.Tcp.connect "127.0.0.1" port
  let tls ← Net.tlsClient clientCtx raw "github.com"
  tls.write (Bytes.ofString "hello")
  let response ← tls.read 4096
  tls.close
  checkEq "a request survives the tunnel" (Kleis.Bytes.toStringLossy response) "echo:hello"
  match ← IO.wait serverTask with
  | .ok sni => checkEq "the server read the SNI before choosing a certificate" sni "github.com"
  | .error e => check "the server side completed" false (toString e)

  -- A client that does not trust the CA must fail, or none of the above means
  -- anything.  The system trust store is the right negative case: a locally
  -- minted CA is definitively not in it.
  let (server2, port2) ← Net.Tcp.listen "127.0.0.1" 0
  let rejectTask ← IO.asTask (prio := .dedicated) do
    let raw ← Net.Tcp.accept server2
    try
      let (hello, sni) ← Proxy.peekSni raw
      let ctx ← cache.contextFor (sni.getD "localhost")
      let tls ← Net.tlsServer ctx raw hello
      tls.close
    catch _ => raw.close
  let strictCtx ← Net.Tls.mkClientContext ""
  let raw2 ← Net.Tcp.connect "127.0.0.1" port2
  let rejected ← try
      let _ ← Net.tlsClient strictCtx raw2 "github.com"
      pure false
    catch _ => pure true
  -- Closing is what lets the server side see the end and stop; a test that
  -- leaks a blocked thread hangs the whole run at exit.
  raw2.close
  let _ ← IO.wait rejectTask
  check "an untrusted CA is rejected by the client" rejected

end KleisTests
