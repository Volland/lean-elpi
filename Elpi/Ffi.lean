import Lean.Data.Json
import Elpi.Runtime.Api

/-!
# C ABI

The foreign-function layer behind the Python and Rust bindings. Programs live in a
handle table inside the Lean runtime; every export takes and returns plain strings and
integers, and answers are JSON text, so no Lean object ever crosses the boundary.
-/

-- @lat: [[components#C ABI]]

namespace Elpi.Ffi

open Lean (Json)

/-- Live programs, indexed by handle. Freed slots hold `none` and are reused. -/
initialize programs : IO.Ref (Array (Option CompiledProgram)) ← IO.mkRef #[]

private def store (p : CompiledProgram) : IO UInt64 := do
  -- One atomic step: concurrent callers must never be handed the same slot.
  programs.modifyGet fun a =>
    match a.findIdx? (·.isNone) with
    | some i => (i.toUInt64, a.set! i (some p))
    | none => (a.size.toUInt64, a.push (some p))

/-- Look a handle up; a stale or never-issued handle is an error, not a crash. -/
private def lookup (h : UInt64) : IO CompiledProgram := do
  match (← programs.get)[h.toNat]? with
  | some (some p) => return p
  | _ => throw (IO.userError s!"invalid program handle {h}")

/-- Parse, typecheck and compile `src`; returns a new handle. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Runtime program loading]]
-- @tg: implements:: [[openspec:language-bindings#Handle-based C ABI]]
@[export leanelpi_ffi_load]
def load (src : String) : IO UInt64 := do
  match Program.load src with
  | .ok p => store p
  | .error e => throw (IO.userError (toString e))

/-- Append clauses to a program; the original handle stays valid. Returns the new handle. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Persistent program extension]]
@[export leanelpi_ffi_assert]
def assertClause (h : UInt64) (clause : String) : IO UInt64 := do
  match (← lookup h).assert clause with
  | .ok p => store p
  | .error e => throw (IO.userError (toString e))

/-- Release a handle. Freeing twice, or freeing an unknown handle, is a no-op. -/
@[export leanelpi_ffi_free]
def free (h : UInt64) : IO Unit :=
  programs.modify fun a => if h.toNat < a.size then a.set! h.toNat none else a

private def solutionJson (s : Solution) : Json :=
  Json.mkObj [
    ("bindings", Json.mkObj (s.bindings.map fun (n, t) => (n, Json.str (s.show t)))),
    ("constraints", Json.arr (s.constraintLines.toArray.map Json.str))]

/-- Run a query and collect at most `limit` solutions (`0` means all) as JSON:
`{"solutions":[{"bindings":{"X":"42"},"constraints":[]}],"exhausted":true}`.
`exhausted` is false when the limit cut the search short. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#IO queries]]
@[export leanelpi_ffi_solve]
def solve (h : UInt64) (query : String) (limit : UInt64) (fuel : UInt64) : IO String := do
  let p ← lookup h
  let st ← solveIO p query (if fuel == 0 then defaultFuel else fuel.toNat)
  let mut out : Array Json := #[]
  let mut exhausted := true
  repeat
    if limit != 0 && out.size.toUInt64 >= limit then
      exhausted := false
      break
    match ← st.next with
    | none => break
    | some s => out := out.push (solutionJson s)
  return (Json.mkObj [("solutions", Json.arr out), ("exhausted", Json.bool exhausted)]).compress

/-- The library version, for binding-side compatibility checks. -/
@[export leanelpi_ffi_version]
def version : String := "0.3.2"

end Elpi.Ffi
