import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-libraries#Lake-aware library resolution#Library from a dependency package is resolved]]
#eval show IO Unit from do
  withTmp fun root => do
    let app := root / "app"
    let lib := root / "app" / ".lake" / "packages" / "utils" / "lib" / "elpi" / "utils"
    IO.FS.createDirAll lib
    IO.FS.writeFile (lib / "lists.elpi") "pred twice i:list A, o:list A.\ntwice L R :- std.append L L R.\n"
    IO.FS.writeFile (app / "lake-manifest.json")
      "{\"version\": \"1.3.0\", \"packagesDir\": \".lake/packages\", \"packages\": [{\"name\": \"utils\", \"type\": \"path\"}], \"name\": \"app\"}"
    IO.FS.writeFile (app / "main.elpi") "accumulate utils/lists.\n"
    match ← Program.loadFile (app / "main.elpi") { pkgRoot := app } with
    | .error e => fail s!"{e}"
    | .ok p => expectEq (← sols p "twice [1] L") ["L = [1, 1]"] "twice [1] L"
    -- an unresolved accumulation lists the searched directories
    IO.FS.writeFile (app / "bad.elpi") "accumulate nowhere.\n"
    match ← Program.loadFile (app / "bad.elpi") { pkgRoot := app } with
    | .ok _ => fail "the unresolved accumulation must be an error"
    | .error e => check (hasSub (toString e) "nowhere") s!"{e}"
