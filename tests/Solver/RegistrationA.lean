import Elpi

/-! Builtins declared by attribute in a module that other test modules import. -/

open Elpi

/-- Counts calls of `between`, to observe how often its implementation runs. -/
initialize betweenCalls : IO.Ref Nat ← IO.mkRef 0

@[noinline] unsafe def bumpBetween (n : Int) : Int := unsafeBaseIO (do betweenCalls.modify (· + 1); pure n)
@[implemented_by bumpBetween] opaque noteBetween (n : Int) : Int

@[elpi_builtin "double" "pred double i:int, o:int."]
def doubleImpl (args : Array Term) : LazyList (Array Term) :=
  match args[0]! with
  | .lit (.int n) => LazyList.ofList [#[.lit (.int (2 * n))]]
  | _ => .nil

@[elpi_builtin "between" "pred between i:int, i:int, o:int."]
def betweenImpl (args : Array Term) : LazyList (Array Term) :=
  match args[0]!, args[1]! with
  | .lit (.int a), .lit (.int b) =>
    let a := noteBetween a
    LazyList.ofList ((List.range (b - a + 1).toNat).map fun k => #[.lit (.int (a + Int.ofNat k))])
  | _, _ => .nil

@[elpi_builtin "succ" "pred succ i:int, o:int."]
def succImpl (args : Array Term) : LazyList (Array Term) :=
  match args[0]! with
  | .lit (.int n) => LazyList.ofList [#[.lit (.int (n + 1))]]
  | _ => .nil

@[elpi_builtin "mk-mvar" "pred mk-mvar."]
def mkMVarImpl (_ : Array Term) : Lean.Meta.MetaM (LazyList (Array Term)) := do
  let _ ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``Nat)
  return LazyList.ofList [#[]]
