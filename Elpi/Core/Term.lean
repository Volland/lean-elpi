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

/-- Substitute `args` for the levels `d, d+1, …, d+n-1` at once in `t` (which lives at depth
`d+n+k`), lowering levels `≥ d+n` by `n`: `subst` for several arguments in one traversal. Each
`args[i]` lives at depth `d`. The result lives at depth `d+k`. -/
partial def substN (t : Term) (d : Nat) (args : Array Term) (k : Nat) : Term :=
  let n := args.size
  match t with
  | .bound l =>
    if l < d then t
    else if l < d + n then args[l - d]!.shiftUp d k
    else .bound (l - n)
  | .app h as =>
    let as' := as.map (substN · d args k)
    match h with
    | .bound l =>
      if d ≤ l && l < d + n then applyAt (args[l - d]!.shiftUp d k) as' (d + k)
      else .app (substN h d args k) as'
    | _ => .app h as'
  | .lam b => .lam (substN b d args (k + 1))
  | .uvar u as => .uvar u (as.map (substN · d args k))
  | .cvar i as => .cvar i (as.map (substN · d args k))
  | t => t

/-- Apply `f` (living at depth `D`) to `args`, β-reducing when `f` is a `lam`. All the
arguments that meet a λ are substituted in one pass. -/
partial def applyAt (f : Term) (args : Array Term) (D : Nat) : Term :=
  if args.isEmpty then f else
  match f with
  | .lam _ =>
    -- peel as many λs as there are arguments
    let rec peel (t : Term) (m : Nat) : Term × Nat :=
      match t with
      | .lam b => if m < args.size then peel b (m + 1) else (t, m)
      | _ => (t, m)
    let (body, m) := peel f 0
    let r := substN body D (if m == args.size then args else args.extract 0 m) 0
    if m == args.size then r else applyAt r (args.extract m args.size) D
  | _ => mkApp f args
end

/-- Rename a stored clause/rule term for use at depth `d`: clause variables become the
given terms and every bound level moves by `d` (the internal binders of a closed term).
A clause variable bound to a term that lives at depth `d` (not to a unification variable)
is relocated to the depth of its occurrence, `d` plus the binders crossed. -/
partial def renameCVars (vars : Array Term) (d : Nat) (t : Term) : Term := go 0 t
where
  go (k : Nat) : Term → Term
    | .bound l => .bound (l + d)
    | .cvar i args =>
      let args' := args.map (go k)
      match vars[i]! with
      | .uvar u us => if args'.isEmpty then .uvar u us else mkApp (.uvar u us) args'
      | v =>
        let v := v.shiftUp d k
        if args'.isEmpty then v else
        match v with
        | .lam _ => applyAt v args' (d + k)
        | _ => mkApp v args'
    | .app h as => .app (go k h) (as.map (go k))
    | .lam b => .lam (go (k + 1) b)
    | .uvar u as => .uvar u (as.map (go k))
    | t => t

/-- Instantiate level `d` of a body living at depth `d+1` with `a` (living at depth `d`). -/
def instantiate (body : Term) (d : Nat) (a : Term) : Term := subst body d a 0

end Term

/-- First-argument key of a clause head or of a call. -/
inductive Key where
  | const (c : ConstId)
  | int (i : Int)
  | str (s : String)
  /-- An eigenvariable (a `pi`-bound name): it is rigid and equal only to itself. -/
  | bound (l : Nat)
  | flex
  deriving BEq, Hashable, Inhabited

/-- Can a clause with first-argument key `k` match a call whose first argument has key `k'`?
Only when neither is a variable and they differ is the answer no. -/
def Key.compatible (k k' : Key) : Bool :=
  match k, k' with
  | .flex, _ | _, .flex => true
  | _, _ => k == k'

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
