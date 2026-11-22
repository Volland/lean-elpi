import Lean.Data.Json
import Elpi.Runtime.Api

/-!
# C ABI

The foreign-function layer behind the Python and Rust bindings. Programs live in a
handle table inside the Lean runtime; every export takes and returns plain strings and
integers, and answers are JSON text, so no Lean object ever crosses the boundary. Host
predicates call back into C through one function pointer and an opaque context per run.
-/

-- @lat: [[components#C ABI]]

namespace Elpi.Ffi

open Lean (Json JsonNumber)

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

/-! ### Terms as JSON trees

`{"c":"name"}` a constant, `{"c":"name","a":[…]}` a constant applied, `{"i":42}`, `{"f":1.5}`,
`{"s":"text"}` literals, `{"v":"X"}` an unassigned variable, and `{"o":"printed"}` anything
else (λ-terms, applied variables, eigenvariables). -/

private def printed (syms : Symbols) (st : Store) (d : Nat) (t : Term) : Json :=
  Json.mkObj [("o", Json.str ((Print.pp t d 0 true).run' { syms, store := st }))]

/-- A zonked term as a JSON tree, at depth `d`. -/
-- @tg: implements:: [[openspec:language-bindings#Structured answers]]
partial def termJson (syms : Symbols) (st : Store) (d : Nat) (t : Term) : Json :=
  match st.deref t d with
  | .const c => Json.mkObj [("c", Json.str (syms.name c))]
  | .app (.const c) args =>
    Json.mkObj [("c", Json.str (syms.name c)), ("a", Json.arr (args.map (termJson syms st d)))]
  | .lit (.int i) => Json.mkObj [("i", Json.num (JsonNumber.fromInt i))]
  | .lit (.float f) =>
    match JsonNumber.fromFloat? f with
    | .inr n => Json.mkObj [("f", Json.num n)]
    | .inl _ => printed syms st d (.lit (.float f))
  | .lit (.str s) => Json.mkObj [("s", Json.str s)]
  | .uvar u #[] =>
    let n := match st.nameOf u with
      | some n => if n.startsWith "_" then s!"_V{u.idx}" else n
      | none => s!"_V{u.idx}"
    Json.mkObj [("v", Json.str n)]
  | t => printed syms st d t

/-- A term of a host answer: constants (known to the program), applications of constants and
literals only. -/
partial def termOfJson (syms : Symbols) (j : Json) : Except String Term := do
  if let .ok n := j.getObjVal? "c" then
    let n ← n.getStr?
    let some c := syms.find? n | throw s!"unknown constant '{n}'"
    match j.getObjVal? "a" with
    | .ok a =>
      let args ← (← a.getArr?).mapM (termOfJson syms)
      return Term.mkApp (.const c) args
    | .error _ => return .const c
  if let .ok v := j.getObjVal? "i" then
    let n ← v.getNum?
    unless n.exponent == 0 do throw s!"not an integer: {v.compress}"
    return ← encodeInt n.mantissa
  if let .ok v := j.getObjVal? "f" then
    return .lit (.float (← v.getNum?).toFloat)
  if let .ok v := j.getObjVal? "s" then
    return .lit (.str (← v.getStr?))
  throw s!"not a host term (expected c, a, i, f or s): {j.compress}"

private def solutionJson (s : Solution) : Json :=
  Json.mkObj [
    ("bindings", Json.mkObj (s.bindings.map fun (n, t) => (n, Json.str (s.show t)))),
    ("terms", Json.mkObj (s.bindings.map fun (n, t) => (n, termJson s.syms s.store 0 t))),
    ("constraints", Json.arr (s.constraintLines.toArray.map Json.str))]

/-! ### Host callbacks -/

/-- Call the C host function `fn` with context `ctx` (both pointers): `none` means no rows.
Implemented in `ffi/leanelpi.c`, which frees the string the host returned. -/
@[extern "leanelpi_host_call"]
opaque hostCall (fn ctx : USize) (name args : @& String) : IO (Option String)

/-- Decode a host answer into one output tuple per row, or the host's error. -/
private def hostRows (syms : Symbols) (nOut : Nat) (txt : String) :
    Except String (List (Array Term)) := do
  let j ← Json.parse txt
  if let .ok e := j.getObjVal? "error" then
    throw (match e with | .str m => m | e => e.compress)
  let rows ← (← j.getObjVal? "rows").getArr?
  let mut out : Array (Array Term) := #[]
  for r in rows do
    let ts ← r.getArr?
    unless ts.size == nOut do
      throw s!"a row has {ts.size} terms, expected {nOut} (one per output argument)"
    out := out.push (← ts.mapM (termOfJson syms))
  return out.toList

/-- The `Builtin IO` that answers the host predicate `sig` through `fn`. -/
-- @tg: implements:: [[openspec:language-bindings#Host callback predicates]]
def hostBuiltin (fn ctx : USize) (sig : BuiltinSig) : Builtin IO :=
  { sig
    run := fun c args => do
      let isOut (i : Nat) := sig.modes.getD i Mode.o == Mode.o
      let nOut := (List.range args.size).countP isOut
      let js := Json.arr (args.map fun a => termJson c.syms c.store c.depth (c.store.zonk a c.depth))
      match ← hostCall fn ctx sig.name js.compress with
      | none => return .fail
      | some txt =>
        match hostRows c.syms nOut txt with
        | .error msg => return .error s!"host predicate '{sig.name}': {msg}"
        | .ok rows =>
          let full (outs : Array Term) : Array Term := Id.run do
            let mut k := 0
            let mut out : Array Term := #[]
            for i in [0:args.size] do
              if isOut i then
                out := out.push outs[k]!
                k := k + 1
              else out := out.push args[i]!
            return out
          return .alts c.store (LazyList.ofList (rows.map full)) }

/-- Declare a host predicate from signature source; returns a new handle. -/
-- @tg: implements:: [[openspec:language-bindings#Host callback predicates]]
@[export leanelpi_ffi_declare]
def declare (h : UInt64) (name sigSrc : String) : IO UInt64 := do
  match (← lookup h).declareHost name sigSrc with
  | .ok p => store p
  | .error e => throw (IO.userError (toString e))

/-- Run a prepared query with `extra` builtins, collecting at most `limit` solutions (`0`
means all). Out of fuel is an error whose message starts with "out of fuel". -/
private def collect (p : CompiledProgram) (query : String) (limit fuel : UInt64)
    (extra : List (Builtin IO)) : IO String := do
  let budget := if fuel == 0 then defaultFuel else fuel.toNat
  let prep ← match p.prepare query budget with
    | .ok prep => pure prep
    | .error e => throw (IO.userError (toString e))
  let base := p.env IO prep.syms
  let env : Env IO :=
    { base with builtins := extra.foldl (init := base.builtins) fun m b =>
        match prep.syms.find? b.sig.name with
        | some c => m.insert c.idx b
        | none => m }
  let mut cur : Machine Unit := prep.machine
  let mut out : Array Json := #[]
  let mut exhausted := true
  let mut left := budget
  repeat
    if limit != 0 && out.size.toUInt64 >= limit then
      exhausted := false
      break
    match ← runLoop env cur with
    | .yield sol M' =>
      out := out.push (solutionJson (mkSolution prep.syms prep.names sol))
      cur := M'
      left := M'.fuel
    | .exhausted _ f => left := f; break
    | .outOfFuel | .paused _ => throw (IO.userError s!"out of fuel: the budget of {budget} steps ran out")
    | .error e => throw (IO.userError (toString e))
  return (Json.mkObj [("solutions", Json.arr out), ("exhausted", Json.bool exhausted),
                      ("fuelUsed", Json.num (JsonNumber.fromNat (budget - left)))]).compress

/-- Run a query and collect at most `limit` solutions (`0` means all) as JSON:
`{"solutions":[{"bindings":{"X":"42"},"terms":{"X":{"i":42}},"constraints":[]}],
"exhausted":true,"fuelUsed":7}`. `exhausted` is false when the limit cut the search short.
A declared host predicate is an error here (there is no callback). -/
-- @tg: implements:: [[openspec:elpi-runtime-library#IO queries]]
@[export leanelpi_ffi_solve]
def solve (h : UInt64) (query : String) (limit : UInt64) (fuel : UInt64) : IO String := do
  collect (← lookup h) query limit fuel []

/-- Like `solve`, but every declared host predicate calls the C function `fn` with `ctx`
synchronously on this thread. -/
-- @tg: implements:: [[openspec:language-bindings#Host callback predicates]]
@[export leanelpi_ffi_solve_host]
def solveHost (h : UInt64) (query : String) (limit fuel : UInt64) (fn ctx : USize) :
    IO String := do
  let p ← lookup h
  collect p query limit fuel (p.hostPreds.map (hostBuiltin fn ctx))

/-- The library version, for binding-side compatibility checks. -/
@[export leanelpi_ffi_version]
def version : String := "0.4.2"

end Elpi.Ffi
