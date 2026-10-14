import TestUtil
import Lean
open Elpi TestUtil Lean

def roundTrip (e : Expr) : IO Expr := do
  match Reflect.toTerm e with
  | .error m => fail s!"reflect: {m}"
  | .ok t =>
    match Reflect.ofTerm t with
    | .ok e' => pure e'
    | .error m => fail s!"reify: {m}"

-- @tg: verifies:: [[openspec:lean-reflection#Lossless Expr round trip#Round trip preserves universe levels]]
#eval show IO Unit from do
  let u := Level.param `u
  let v := Level.param `v
  let e1 := Expr.const ``List.map [u, v]
  let e2 := Expr.sort (Level.succ (Level.max u v))
  for e in [e1, e2] do
    let e' ← roundTrip e
    check (e.equal e') s!"{e} was not preserved: {e'}"

-- @tg: verifies:: [[openspec:lean-reflection#Lossless Expr round trip#Round trip preserves metadata and projections]]
#eval show IO Unit from do
  let md : MData := KVMap.empty.insert `pp.analysis.skip (DataValue.ofBool true)
  let e := Expr.mdata md (Expr.proj ``Prod 0 (Expr.fvar ⟨`p⟩))
  let e' ← roundTrip e
  check (e.equal e') s!"metadata or projection lost: {e'}"
  -- binder names, binder info, let flags and large literals survive too
  let big := Expr.lit (.natVal (2 ^ 80))
  let l := Expr.letE `y (mkConst ``Nat) big (Expr.lam `x (mkConst ``Nat) (.bvar 1) .implicit) true
  let l' ← roundTrip l
  check (l.equal l') s!"{l'}"

-- every declaration type and value of Init survives the round trip
#eval show CoreM Unit from do
  let env ← getEnv
  let mut checked : Nat := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      if (env.header.moduleNames[idx.toNat]!).toString.startsWith "Init.Core" then
        let es := [some ci.type, ci.value?].filterMap id
        for e in es do
          let e' ← match Reflect.toTerm e with
            | .error m => throwError "{n}: reflect: {m}"
            | .ok t => match Reflect.ofTerm t with
              | .ok e' => pure e'
              | .error m => throwError "{n}: reify: {m}"
          unless e.equal e' do throwError "{n}: round trip changed the term"
          checked := checked + 1
    | none => pure ()
  unless checked > 100 do throwError "too few declarations checked: {checked}"
