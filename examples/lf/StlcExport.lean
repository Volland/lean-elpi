/-!
# STLC export sketch

The Lean export that the LF design (`openspec/changes/add-elpi-lf/design.md`) expects
`lf_export stlc` to print, plus two certificates. It is checked with `lean` today, before
any LF code exists, to confirm that the chosen encoding (well-scoped de Bruijn with
explicit contexts) is accepted by the kernel without axioms.

Check: `lean examples/lf/StlcExport.lean`
-/

-- @lat: [[components#LF export]]

namespace Stlc
inductive Tp : Type where
  | arr  : Tp → Tp → Tp
  | base : Tp

inductive Var : Nat → Type where
  | zero {n} : Var (Nat.succ n)
  | succ {n} : Var n → Var (Nat.succ n)

inductive Tm : Nat → Type where
  | var {n} : Var n → Tm n
  | lam {n} : Tp → Tm (Nat.succ n) → Tm n
  | app {n} : Tm n → Tm n → Tm n

-- world of `of`: one block  b_of (T:tp) : x:tm, u:of x T
inductive Ctx : Nat → Type where
  | nil  : Ctx Nat.zero
  | snoc {n} : Ctx n → Tp → Ctx (Nat.succ n)

inductive Ctx.Lookup : {n : Nat} → Ctx n → Var n → Tp → Prop where
  | here  {n} {Γ : Ctx n} {T}       : Ctx.Lookup (Ctx.snoc Γ T) Var.zero T
  | there {n} {Γ : Ctx n} {S T} {i} : Ctx.Lookup Γ i T → Ctx.Lookup (Ctx.snoc Γ S) (Var.succ i) T

inductive Of : {n : Nat} → Ctx n → Tm n → Tp → Prop where
  | hyp    {n} {Γ : Ctx n} {i : Var n} {T} : Ctx.Lookup Γ i T → Of Γ (Tm.var i) T
  | of_lam {n} {Γ : Ctx n} {T1 : Tp} {E : Tm (Nat.succ n)} {T2 : Tp} :
      Of (Ctx.snoc Γ T1) E T2 → Of Γ (Tm.lam T1 E) (Tp.arr T1 T2)
  | of_app {n} {Γ : Ctx n} {E1 E2 : Tm n} {T2 T1 : Tp} :
      Of Γ E2 T1 → Of Γ E1 (Tp.arr T1 T2) → Of Γ (Tm.app E1 E2) T2
end Stlc

-- certificate from the design, for of_lam base (x\ x) base (x\ u\ u)
theorem cert : Stlc.Of Stlc.Ctx.nil (Stlc.Tm.lam Stlc.Tp.base (Stlc.Tm.var Stlc.Var.zero))
           (Stlc.Tp.arr Stlc.Tp.base Stlc.Tp.base) :=
  @Stlc.Of.of_lam 0 Stlc.Ctx.nil Stlc.Tp.base (@Stlc.Tm.var 1 Stlc.Var.zero) Stlc.Tp.base
    (@Stlc.Of.hyp 1 (Stlc.Ctx.snoc Stlc.Ctx.nil Stlc.Tp.base) Stlc.Var.zero Stlc.Tp.base
      (@Stlc.Ctx.Lookup.here 0 Stlc.Ctx.nil Stlc.Tp.base))

-- paper example: λx:base. λf:base→base. f x
theorem cert2 : Stlc.Of Stlc.Ctx.nil
    (.lam .base (.lam (.arr .base .base) (.app (.var .zero) (.var (.succ .zero)))))
    (.arr .base (.arr (.arr .base .base) .base)) :=
  .of_lam (.of_lam (.of_app (.hyp (.there .here)) (.hyp .here)))

#print axioms cert
#print axioms cert2
