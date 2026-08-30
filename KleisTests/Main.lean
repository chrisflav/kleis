import KleisTests.Util
import KleisTests.Crypto
import KleisTests.Http
import KleisTests.Wire
import KleisTests.Facts
import KleisTests.Externs
import KleisTests.Policy
import KleisTests.Security
import KleisTests.Ca

/-!
# The test driver

Run as a compiled binary rather than through `lean --run`, because the
certificate and TLS tests call into the OpenSSL shim and the interpreter cannot
resolve statically linked symbols.

Everything runs against a temporary `KLEIS_HOME`, so a test never reads or
writes the credentials of whoever is running it.
-/

open KleisTests

def main : IO UInt32 := do
  -- A data directory of our own.  Without this the CA tests would write into
  -- the user's real one.
  let home ← match ← IO.getEnv Kleis.Dirs.homeVar with
    | some h => pure (System.FilePath.mk h)
    | none => do
      let tmp := System.FilePath.mk "." / ".lake" / "test-home"
      IO.FS.createDirAll tmp
      IO.FS.realPath tmp
  Kleis.Dirs.useHome home
  say s!"kleis test suite (home {home})"
  say ""
  utilTests
  cryptoTests
  httpTests
  wireTests
  factsTests
  externTests
  policyTests
  securityTests
  caTests
  tlsTests
  report
