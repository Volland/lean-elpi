import TestUtil
import Lean
open Elpi TestUtil Lean

def reflect (e : Expr) : IO Elpi.Term :=
  match Reflect.toTerm e with
  | .ok t => pure t
  | .error m => fail m

def headConst : Elpi.Term → Option ConstId
  | .app (.const c) _ => some c
  | _ => none

-- @tg: verifies:: [[openspec:lean-reflection#HOAS term encoding#Lean binder becomes an ELPI lambda]]
#eval show IO Unit from do
  -- fun (x : Nat) => x
  let t ← reflect (Expr.lam `x (mkConst ``Nat) (.bvar 0) .default)
  match t with
  | .app (.const c) #[.builtinData b, .app (.const k) #[.builtinData n, _], .lam (.bound 0)] =>
    check (c == cFunR && k == cConstR) "fun N (const \"Nat\" []) (x\\ x)"
    expectEq b.typeName "binder" "binder handle"
    expectEq (Reflect.nameDec n.data) ``Nat "constant name"
  | _ => fail s!"unexpected shape {repr t}"
  -- β-reduction by ELPI: the body applied to `lit (nat 3)` is `lit (nat 3)`
  let p ← load "accumulate lean.\npred beta i:term, o:term.\nbeta T R :- T = fun _ _ F, R = F (lit (nat 3))."
  let q := "beta (fun B (const N []) (x\\ x)) R"
  let _ := q
  match (solve p "T = fun _ _ F, R = F (lit (nat 3)), T = fun _ _ (x\\ x)").toList with
  | [.ok s] =>
    check (s.bindings.lookup "R" == some (Elpi.Term.app (.const cLitR) #[.app (.const cNatLitR) #[.lit (.int 3)]])) "R is lit (nat 3)"
  | _ => fail "expected one solution"

-- @tg: verifies:: [[openspec:lean-reflection#HOAS term encoding#Constructors cover every Expr form]]
#eval show IO Unit from do
  let nat := mkConst ``Nat
  let samples : List (Expr × ConstId) :=
    [ (mkConst ``Nat.zero, cConstR), (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero), cAppR),
      (Expr.lam `x nat (.bvar 0) .default, cFunR), (Expr.forallE `x nat nat .default, cForallR),
      (Expr.letE `x nat (Expr.lit (.natVal 1)) (.bvar 0) false, cLetR), (Expr.sort Level.one, cSortR),
      (Expr.lit (.natVal 7), cLitR), (Expr.lit (.strVal "s"), cLitR), (Expr.mvar ⟨`m⟩, cMVarR), (Expr.fvar ⟨`f⟩, cFVarR),
      (Expr.proj ``Prod 0 (Expr.fvar ⟨`p⟩), cProjR), (Expr.mdata {} nat, cMDataR) ]
  for (e, c) in samples do
    let t ← reflect e
    check (headConst t == some c) s!"head constructor of {e}"
  match Reflect.toTerm (.bvar 0) with
  | .error m => check (hasSub m "loose bound variable") m
  | .ok _ => fail "a loose bvar must fail"
