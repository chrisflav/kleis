import Auth.Dirs
import Auth.Util.Toml
import Std.Time

/-!
# Files on disk

Everything the daemon persists goes through here, for three reasons that are
all the same reason: a file holding a credential must never be readable by
anybody else, must never be half-written, and must never briefly exist with the
wrong permissions.

So a write creates the temporary file empty, restricts it, fills it, and only
then renames it over the target.  A reader either sees the old contents or the
new ones, and at no point does a world-readable file contain a secret.
-/

namespace Auth
namespace Store

open LeanBiscuit (Bytes)

/-- Restrict a path to its owner. -/
def restrict (p : System.FilePath) (mode : String := "600") : IO Unit := do
  let _ ← IO.Process.run { cmd := "chmod", args := #[mode, p.toString] }

/-- Create a directory and everything above it, owner-only. -/
def mkdir (p : System.FilePath) : IO Unit := do
  IO.FS.createDirAll p
  restrict p "700"

/-- Write a file atomically, owner-only.

The order matters: the temporary file is created empty, restricted, and only
then written, so a secret is never present in a file that anybody else could
still open. -/
def writeSecret (p : System.FilePath) (contents : Bytes) : IO Unit := do
  if let some parent := p.parent then mkdir parent
  let tmp := System.FilePath.mk (p.toString ++ ".tmp")
  IO.FS.writeBinFile tmp ByteArray.empty
  restrict tmp
  IO.FS.writeBinFile tmp contents
  IO.FS.rename tmp p

/-- Write a file atomically, without restricting it: for things that are not
secret and that other tools may want to read, such as the CA certificate. -/
def writePublic (p : System.FilePath) (contents : String) : IO Unit := do
  if let some parent := p.parent then IO.FS.createDirAll parent
  let tmp := System.FilePath.mk (p.toString ++ ".tmp")
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp p

/-- Read a file, or `none` if it is not there. -/
def read? (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then pure (some (← IO.FS.readFile p)) else pure none

/-- Read a file as bytes, or `none`. -/
def readBin? (p : System.FilePath) : IO (Option Bytes) := do
  if ← p.pathExists then pure (some (← IO.FS.readBinFile p)) else pure none

/-- Append a line, creating the file if need be. -/
def appendLine (p : System.FilePath) (line : String) : IO Unit := do
  if let some parent := p.parent then mkdir parent
  let existed ← p.pathExists
  let h ← IO.FS.Handle.mk p .append
  h.putStr (line ++ "\n")
  h.flush
  if !existed then restrict p

/-- Every regular file in a directory with the given extension, sorted. -/
def listFiles (dir : System.FilePath) (ext : String) : IO (Array System.FilePath) := do
  if !(← dir.pathExists) then return #[]
  let entries ← dir.readDir
  let matching := entries.filterMap fun e =>
    if e.fileName.endsWith ("." ++ ext) then some e.path else none
  return matching.qsort fun a b => a.toString < b.toString

/-- Read `n` bytes from the system entropy source. -/
def randomBytes (n : Nat) : IO Bytes := do
  IO.FS.withFile "/dev/urandom" .read fun h => h.read n.toUSize

/-- A hex-encoded random identifier. -/
def randomId (bytes : Nat := 12) : IO String := do
  return Bytes.toHex (← randomBytes bytes)

/-- Seconds since the Unix epoch.

The wall clock rather than a monotonic counter: a policy's `time` fact decides
whether a token has expired, and a counter that restarted with the daemon would
let an expired token come back to life. -/
def now : IO Nat := do
  let t ← Std.Time.Timestamp.now
  let s := t.toSecondsSinceUnixEpoch.toInt
  return if s < 0 then 0 else s.toNat

end Store
end Auth
