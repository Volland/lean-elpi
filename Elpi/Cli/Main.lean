/-!
# CLI

The `lean-elpi` executable: upstream-compatible flags (`-exec`, `-test`, `-I`),
`--lean-env` and a REPL. Skeleton only: it reports that the engine is not implemented.
-/

-- @lat: [[components#CLI]]

def main (_args : List String) : IO UInt32 := do
  IO.eprintln "lean-elpi: engine not implemented yet (see openspec/changes/add-elpi-core)"
  return 1
