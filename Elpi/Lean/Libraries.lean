import Lean.Data.Json
import Elpi.Runtime.Api

/-!
# Library resolver

Lake-aware resolution of `accumulate` targets and embedded libraries: the directory of the
accumulating file, explicit include paths, the current package's `lib/elpi/`, the
dependency packages' `lib/elpi/` in manifest order, and finally the libraries embedded in
the running binary.
-/

-- @lat: [[components#Library resolver]]

namespace Elpi.Libraries

open System

/-- Where to look for libraries besides the accumulating file's directory. -/
structure Config where
  includes : List FilePath := []
  /-- Root of the current Lake package (holds `lib/elpi/` and `lake-manifest.json`). -/
  pkgRoot : FilePath := "."

/-- `lib/elpi/` directories of the dependency packages, in `lake-manifest.json` order. -/
def dependencyDirs (root : FilePath) : IO (List FilePath) := do
  let mf := root / "lake-manifest.json"
  unless ← mf.pathExists do return []
  let txt ← IO.FS.readFile mf
  match Lean.Json.parse txt with
  | .error _ => return []
  | .ok j =>
    let pkgs : List Lean.Json :=
      match j.getObjValD "packages" with
      | .arr a => a.toList
      | _ => []
    let dir := (j.getObjValD "packagesDir").getStr?.toOption.getD ".lake/packages"
    return pkgs.filterMap fun p =>
      match (p.getObjValD "name").getStr?.toOption with
      | some n =>
        let clean := (n.replace "«" "").replace "»" ""
        some (root / dir / clean / "lib" / "elpi")
      | none => none

def fileNames (name : String) : List String :=
  if name.endsWith ".elpi" then [name] else [name ++ ".elpi"]

/-- Resolve an accumulate target: the first match in the search order wins; failure lists
the searched directories. Returns the canonical key and the source text. -/
-- @tg: implements:: [[openspec:elpi-libraries#Lake-aware library resolution]]
def resolve (cfg : Config) (name fromFile : String) : IO (Except String (String × String)) := do
  let fromDir : FilePath := (FilePath.mk fromFile).parent.getD "."
  let deps ← dependencyDirs cfg.pkgRoot
  let dirs : List FilePath :=
    [fromDir] ++ cfg.includes ++ [cfg.pkgRoot / "lib" / "elpi"] ++ deps
  for d in dirs do
    for fn in fileNames name do
      let path := d / fn
      if ← path.pathExists then
        if !(← path.isDir) then
          let key ← IO.FS.realPath path
          return .ok (key.toString, ← IO.FS.readFile path)
  match Std.embedded.find? (·.1 == name) with
  | some (n, txt) => return .ok (s!"<embedded>/{n}", txt)
  | none =>
    return .error s!"cannot resolve '{name}'; searched: {", ".intercalate (dirs.map toString)} and the embedded libraries"

end Elpi.Libraries

namespace Elpi.Program

/-- Load a program from a file, resolving accumulations through the library search path. -/
def loadFile (path : System.FilePath) (cfg : Libraries.Config := {})
    (sigs : List String := []) : IO (Except ElpiError CompiledProgram) := do
  if noteParse 0 > 1000000000000 then return .error (.load "parser counter overflow")
  let src ← IO.FS.readFile path
  let find (name from_ : String) : IO (Option (String × String)) := do
    match ← Libraries.resolve cfg name from_ with
    | .ok r => return some r
    | .error _ => return none
  match baseProgram with
  | .error e => return .error e
  | .ok base =>
    match ← loadUnits find path.toString src with
    | .error e => return .error (.parse e.toString)
    | .ok ds =>
      let mut pre : List Decl := []
      for sg in sigs do
        match Parser.parseProgram "<signature>" sg with
        | .ok d => pre := pre ++ d
        | .error e => return .error (.parse e.toString)
      return base.addDecls (pre ++ ds)

end Elpi.Program
