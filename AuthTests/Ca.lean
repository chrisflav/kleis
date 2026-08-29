import AuthTests.Harness

/-! # Certificates and TLS

These need the FFI, so they only run in the compiled test binary — the
interpreter cannot resolve statically linked symbols. -/

namespace AuthTests

open Auth LeanBiscuit

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
      serial := 12345, commonName := "example.test", organization := some "auth"
      altNames := ["example.test", "127.0.0.1"]
      notBefore := 1700000000, notAfter := 1800000000, isCa := false }
    match X509.certificate spec point fixedSecret none with
    | .error e => check "a certificate is built and signed" false e
    | .ok der => do
      check "a certificate is built and signed" true
      -- The signature is over the TBS, so it must verify against the key.
      let body := X509.tbs spec point point (X509.name "example.test" (some "auth"))
      check "the certificate is longer than what it signs" (der.size > body.size)
  match X509.privateKeyPem fixedSecret with
  | .error e => check "a private key renders as PEM" false e
  | .ok pem => do
    check "a private key renders as PEM" (pem.startsWith "-----BEGIN PRIVATE KEY-----")
    check "and ends properly" (pem.endsWith "-----END PRIVATE KEY-----\n")

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
    tls.write (Bytes.ofString s!"echo:{Auth.Bytes.toStringLossy request}")
    tls.close
    pure (sni.getD "")

  let clientCtx ← Net.Tls.mkClientContext caFile
  let raw ← Net.Tcp.connect "127.0.0.1" port
  let tls ← Net.tlsClient clientCtx raw "github.com"
  tls.write (Bytes.ofString "hello")
  let response ← tls.read 4096
  tls.close
  checkEq "a request survives the tunnel" (Auth.Bytes.toStringLossy response) "echo:hello"
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

end AuthTests
