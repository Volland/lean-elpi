/-!
# Term store

Terms: constants, de Bruijn-level bound variables, applications, λ, unification variables
with scope levels, literals and opaque host data, plus the level-relocating `move`
(`shiftUp`), substitution and β-reduction that the unifier and the machine share.

A term living at depth `d` mentions levels `0 … d-1`; a `lam` met at depth `d` binds
level `d`. Clause terms additionally use `cvar` for clause-level variables, which are
renamed to fresh unification variables when the clause is selected.
-/

-- @lat: [[components#Term store]]

namespace Elpi

instance : Hashable Float := ⟨fun f => hash f.toString⟩

/-- Interned global constant (predicate, constructor, builtin). -/
structure ConstId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited

/-- Unification variable; its scope level lives in the store. -/
structure UVarId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited

inductive Literal where
  | int (i : Int)
  | float (f : Float)
  | str (s : String)
  deriving BEq, Hashable, Repr, Inhabited

/-- Host data carried through ELPI untouched (compared by handle). -/
structure Opaque where
  handle : Nat
  typeName : String
  /-- Canonical encoding of the host value; equal data means equal values. -/
  data : String := ""
  deriving BEq, Hashable, Repr, Inhabited

-- @tg: implements:: [[openspec:elpi-core-engine#Term representation]]
inductive Term where
  | const (c : ConstId)
  /-- de Bruijn level: λ-bound variable or eigenvariable. -/
  | bound (lvl : Nat)
  /-- Head is `const` or `bound`; never `app`, `lam` or `uvar`. -/
  | app (h : Term) (args : Array Term)
  /-- Binds the level equal to the depth at which the `lam` sits. -/
  | lam (body : Term)
  /-- A unification variable applied to a spine (possibly empty). -/
  | uvar (u : UVarId) (args : Array Term)
  /-- Clause-level variable, only inside stored clauses. -/
  | cvar (i : Nat) (args : Array Term)
  | lit (l : Literal)
  | builtinData (d : Opaque)
  deriving BEq, Hashable, Repr, Inhabited

namespace Term

/-- Spine application `h a1 … an` of a rigid head; collapses empty spines. -/
def mkApp (h : Term) (args : Array Term) : Term :=
  if args.isEmpty then h else
  match h with
  | .app h' as => .app h' (as ++ args)
  | .uvar u as => .uvar u (as ++ args)
  | .cvar i as => .cvar i (as ++ args)
  | _ => .app h args

/-- Relocate: increase every level `≥ d` by `k` (the "move" of binders when a term built
at depth `d` is used `k` levels deeper). -/
partial def shiftUp (t : Term) (d k : Nat) : Term :=
  if k == 0 then t else go t
where
  go : Term → Term
    | .bound l => if l ≥ d then .bound (l + k) else .bound l
    | .app h as => .app (go h) (as.map go)
    | .lam b => .lam (go b)
    | .uvar u as => .uvar u (as.map go)
    | .cvar i as => .cvar i (as.map go)
    | t => t

mutual
/-- Substitute `a` for level `d` in `t` (which lives at depth `d+1+k`), lowering levels
`> d` by one and re-normalising applications whose head was substituted. `a` lives at
depth `d`. The result lives at depth `d+k`. -/
partial def subst (t : Term) (d : Nat) (a : Term) (k : Nat := 0) : Term :=
  match t with
  | .bound l =>
    if l < d then t
    else if l == d then a.shiftUp d k
    else .bound (l - 1)
  | .app h as =>
    let as' := as.map (subst · d a k)
    match h with
    | .bound l =>
      if l == d then applyAt (a.shiftUp d k) as' (d + k)
      else .app (subst h d a k) as'
    | _ => .app h as'
  | .lam b => .lam (subst b d a (k + 1))
  | .uvar u as => .uvar u (as.map (subst · d a k))
  | .cvar i as => .cvar i (as.map (subst · d a k))
  | t => t

/-- Apply `f` (living at depth `D`) to `args`, β-reducing when `f` is a `lam`. -/
partial def applyAt (f : Term) (args : Array Term) (D : Nat) : Term :=
  if args.isEmpty then f else
  match f with
  | .lam b =>
    let r := subst b D args[0]!
    applyAt r (args.extract 1 args.size) D
  | _ => mkApp f args
end

/-- Rename a stored clause/rule term for use at depth `d`: clause variables become the
given terms and every bound level moves by `d` (the internal binders of a closed term). -/
partial def renameCVars (vars : Array Term) (d : Nat) : Term → Term
  | .bound l => .bound (l + d)
  | .cvar i args => mkApp vars[i]! (args.map (renameCVars vars d))
  | .app h as => .app (renameCVars vars d h) (as.map (renameCVars vars d))
  | .lam b => .lam (renameCVars vars d b)
  | .uvar u as => .uvar u (as.map (renameCVars vars d))
  | t => t

/-- Instantiate level `d` of a body living at depth `d+1` with `a` (living at depth `d`). -/
def instantiate (body : Term) (d : Nat) (a : Term) : Term := subst body d a 0

end Term

/-- Errors raised while loading or running a program. `outOfFuel` is a resource error,
distinct from failure. -/
inductive ElpiError where
  | parse (msg : String)
  | type (msg : String)
  | load (msg : String)
  | runtime (msg : String)
  | outOfFuel
  deriving Inhabited, Repr

def ElpiError.toString : ElpiError → String
  | .parse m => m
  | .type m => m
  | .load m => m
  | .runtime m => m
  | .outOfFuel => "resource error: out of fuel"

instance : ToString ElpiError := ⟨ElpiError.toString⟩

/-- A lazy list with memoised tails; Lean core has none. -/
inductive LazyList (α : Type) where
  | nil : LazyList α
  | cons (a : α) (tl : Thunk (LazyList α)) : LazyList α

instance {α : Type} : Inhabited (LazyList α) := ⟨.nil⟩

namespace LazyList

variable {α : Type}

def head? : LazyList α → Option α
  | nil => none
  | cons a _ => some a

/-- First `n` elements, forcing only what is needed. -/
def take : LazyList α → Nat → List α
  | _, 0 => []
  | nil, _ => []
  | cons a tl, n + 1 => a :: take tl.get n

/-- Force the whole list (diverges on infinite lists). -/
partial def toList : LazyList α → List α
  | nil => []
  | cons a tl => a :: toList tl.get

def ofList : List α → LazyList α
  | [] => nil
  | a :: as => cons a (Thunk.mk fun _ => ofList as)

end LazyList

end Elpi
