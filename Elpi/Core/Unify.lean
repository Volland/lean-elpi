import Elpi.Core.Store

/-!
# Unifier

Higher-order pattern unification over the persistent store: rigid–rigid decomposition
with λ-descent and η-expansion, flex–rigid inversion with pruning and an occurs check,
flex–flex, and suspension of problems outside the pattern fragment. Argument spines are
processed through an explicit worklist so long lists do not use native stack.
-/

-- @lat: [[components#Unifier]]

namespace Elpi

/-- Outcome of inverting a term into the scope of a variable. -/
inductive InvR (α : Type) where
  | ok (s : Store) (a : α)
  | fail
  | delay

instance {α : Type} : Inhabited (InvR α) := ⟨.fail⟩

/-- What inversion needs to know about the variable being assigned. -/
structure InvCtx where
  x : UVarId
  /-- Scope level ℓ of `x`. -/
  lvl : Nat
  /-- The distinct levels of `x`'s pattern spine. -/
  spine : Array Nat
  /-- Depth at which the problem is solved. -/
  d : Nat

namespace Unify

/-- A spine is a pattern when it consists of distinct bound levels. -/
def patternSpine (s : Store) (args : Array Term) (d : Nat) : Option (Array Nat) := Id.run do
  let mut out : Array Nat := #[]
  for a in args do
    match s.deref a d with
    | .bound l =>
      if out.contains l then return none
      out := out.push l
    | _ => return none
  return some out

/-- `lam^m body` as a term. -/
def lams (m : Nat) (body : Term) : Term :=
  (List.range m).foldl (fun b _ => .lam b) body

mutual
/-- Express `t` (at depth `c.d + k`) in the scope of `c.x`: its spine levels become the
binders of the abstraction, levels below ℓ are kept, other eigenvariables make the
problem unsolvable. Variables met on the way are pruned as needed. -/
partial def inv (c : InvCtx) (s : Store) (t : Term) (k : Nat) : InvR Term :=
  let n := c.spine.size
  let t := s.deref t (c.d + k)
  match t with
  | .const _ | .lit _ | .builtinData _ => .ok s t
  | .bound l =>
    if l ≥ c.d then .ok s (.bound (l - c.d + c.lvl + n))
    else
      match c.spine.findIdx? (· == l) with
      | some i => .ok s (.bound (c.lvl + i))
      | none => if l < c.lvl then .ok s t else .fail
  | .lam b =>
    match inv c s b (k + 1) with
    | .ok s b' => .ok s (.lam b')
    | .fail => .fail
    | .delay => .delay
  | .app h as =>
    match inv c s h k with
    | .ok s h' =>
      match invArr c s as k with
      | .ok s as' => .ok s (.app h' as')
      | .fail => .fail
      | .delay => .delay
    | .fail => .fail
    | .delay => .delay
  | .cvar _ _ => .fail
  | .uvar y ys =>
    if y == c.x then .fail
    else
      let ℓy := s.levelOf y
      -- map each argument, remembering which survive
      let m := ys.size
      let rec go (i : Nat) (s : Store) (kept : Array Nat) (outs : Array Term) : Store × Array Nat × Array Term :=
        if h : i < m then
          match inv c s ys[i] k with
          | .ok s' a => go (i + 1) s' (kept.push i) (outs.push a)
          | _ => go (i + 1) s kept outs
        else (s, kept, outs)
      let (s1, kept, outs) := go 0 s #[] #[]
      if kept.size == m && ℓy ≤ c.lvl then .ok s1 (.uvar y outs)
      else
        -- pruning needs the spine of `y` to be a pattern whenever an argument is dropped
        if kept.size != m && (patternSpine s ys (c.d + k)).isNone then .delay
        else
          let ℓ' := min ℓy c.lvl
          let (y', s2) := s1.fresh ℓ' (s1.nameOf y)
          let val := lams m (.uvar y' (kept.map fun i => .bound (ℓy + i)))
          let s3 := s2.setAssign y val
          .ok s3 (.uvar y' outs)

partial def invArr (c : InvCtx) (s : Store) (xs : Array Term) (k : Nat) : InvR (Array Term) :=
  let rec go (i : Nat) (s : Store) (acc : Array Term) : InvR (Array Term) :=
    if h : i < xs.size then
      match inv c s xs[i] k with
      | .ok s' a => go (i + 1) s' (acc.push a)
      | .fail => .fail
      | .delay => .delay
    else .ok s acc
  go 0 s #[]
end

/-- Assign `x xs := t` by inversion. `none` means "no solution" (clash); `some (inl _)`
a delay; `some (inr s)` success. -/
def solveFlex (s : Store) (x : UVarId) (xs : Array Term) (t : Term) (d : Nat) :
    InvR Unit :=
  match patternSpine s xs d with
  | none => .delay
  | some spine =>
    let c : InvCtx := { x, lvl := s.levelOf x, spine, d }
    match inv c s t 0 with
    | .ok s' t' => .ok (s'.setAssign x (lams spine.size t')) ()
    | .fail => .fail
    | .delay => .delay

/-- η-expansion step for a term meeting a λ at depth `d`. -/
def etaApp (t : Term) (d : Nat) : Term := Term.mkApp (t.shiftUp d 1) #[.bound d]

abbrev Eqn := Term × Term × Nat

/-- Unassigned variables occurring in `t` (flexible heads and arguments), without repeats. -/
partial def collectUVars (s : Store) (t : Term) (d : Nat) (acc : Array UVarId := #[]) :
    Array UVarId :=
  match s.deref t d with
  | .uvar u as =>
    let acc := if acc.contains u then acc else acc.push u
    as.foldl (fun a x => collectUVars s x d a) acc
  | .app h as => as.foldl (fun a x => collectUVars s x d a) (collectUVars s h d acc)
  | .lam b => collectUVars s b (d + 1) acc
  | _ => acc

/-- Head constant of a rigid term, if any. -/
def headConst : Term → Option ConstId
  | .const c => some c
  | .app (.const c) _ => some c
  | _ => none

/-- Reserved index of the constant `=` (see `reservedNames`). -/
def eqConst : ConstId := ⟨8⟩

/-- Can this variable be assigned (match mode protects goal variables)? -/
def assignable (protect : Nat) (u : UVarId) : Bool := u.idx ≥ protect

partial def loop (protect : Nat) (s : Store) : List Eqn → Option Store
  | [] => some s
  | (a, b, d) :: rest =>
    let a := s.deref a d
    let b := s.deref b d
    -- suspend the problem as the goal `a = b` keyed on its variables (woken on assignment)
    let delayIt : Unit → Option Store := fun _ =>
      let keys := collectUVars s b d (collectUVars s a d)
      let (_, cs) := s.cstore.add
        { id := 0, goal := .app (.const eqConst) #[a, b], keys, depth := d, locals := [],
          pred := none }
      loop protect { s with cstore := cs } rest
    -- consult the hooks (only now: pattern unification could not decide the problem)
    let tryHooks : Bool → Unit → Option Store := fun declineFails _ =>
      let rec go (i : Nat) : Option Store :=
        if h : i < s.hooks.size then
          match s.hooks[i].onStuck (s.deref · d) a b d with
          | .decline => go (i + 1)
          | .fail => none
          | .suspend => delayIt ()
          | .solved θ => loop protect s (θ.map (fun (u, t) => (Term.uvar u #[], t, d)) ++ rest)
        else if declineFails then none else delayIt ()
      go 0
    let interpreted : Bool :=
      match headConst a, headConst b with
      | some c, _ => s.interp.contains c.idx
      | _, some c => s.interp.contains c.idx
      | _, _ => false
    let clash : Unit → Option Store := fun _ =>
      if interpreted && !s.hooks.isEmpty then tryHooks true () else none
    match a, b with
    | .uvar x xs, .uvar y ys =>
      if x == y then
        if xs == ys then loop protect s rest
        else
          match patternSpine s xs d, patternSpine s ys d with
          | some px, some py =>
            if px.size != py.size || !assignable protect x then none else
            let ℓ := s.levelOf x
            let n := px.size
            let kept := (List.range n).filter (fun i => px[i]! == py[i]!) |>.toArray
            let (x', s1) := s.fresh ℓ (s.nameOf x)
            let val := lams n (.uvar x' (kept.map fun i => .bound (ℓ + i)))
            loop protect (s1.setAssign x val) rest
          | _, _ => tryHooks false ()
      else
        let px := patternSpine s xs d
        let py := patternSpine s ys d
        let xOk := px.isSome && assignable protect x
        let yOk := py.isSome && assignable protect y
        let pickX :=
          if xOk && yOk then
            let lx := s.levelOf x; let ly := s.levelOf y
            lx > ly || (lx == ly && x.idx ≥ y.idx)
          else xOk
        if pickX || yOk then
          let r := if pickX then solveFlex s x xs b d else solveFlex s y ys a d
          match r with
          | .ok s' () => loop protect s' rest
          | .fail => none
          | .delay => if assignable protect x || assignable protect y then tryHooks false () else none
        else if !assignable protect x && !assignable protect y then none
        else tryHooks false ()
    | .uvar x xs, t =>
      if !assignable protect x then none else
      match solveFlex s x xs t d with
      | .ok s' () => loop protect s' rest
      | .fail => none
      | .delay => tryHooks false ()
    | t, .uvar y ys =>
      if !assignable protect y then none else
      match solveFlex s y ys t d with
      | .ok s' () => loop protect s' rest
      | .fail => none
      | .delay => tryHooks false ()
    | .lam x, .lam y => loop protect s ((x, y, d + 1) :: rest)
    | .lam x, t => loop protect s ((x, etaApp t d, d + 1) :: rest)
    | t, .lam y => loop protect s ((etaApp t d, y, d + 1) :: rest)
    | .const c, .const c' => if c == c' then loop protect s rest else clash ()
    | .bound l, .bound l' => if l == l' then loop protect s rest else none
    | .lit l, .lit l' => if l == l' then loop protect s rest else none
    | .builtinData o, .builtinData o' => if o == o' then loop protect s rest else none
    | .app h as, .app h' as' =>
      if as.size != as'.size then clash () else
      let hOk :=
        match h, h' with
        | .const c, .const c' => c == c'
        | .bound l, .bound l' => l == l'
        | _, _ => false
      if !hOk then clash () else
      let pairs := (as.zip as').toList.map fun (p, q) => (p, q, d)
      loop protect s (pairs ++ rest)
    | _, _ => clash ()

end Unify

/-- Unify `a` and `b` at depth `d`; problems outside the pattern fragment are suspended
as constraints in `Store.cstore`, after the registered hooks (if any) were consulted.
Variables below `Store.protect` are frozen (CHR matching and guards). -/
-- @tg: implements:: [[openspec:elpi-core-engine#Higher-order pattern unification]]
def unify (s : Store) (a b : Term) (d : Nat) : Option Store :=
  Unify.loop s.protect s [(a, b, d)]

/-- Match mode for input arguments: variables with an index below `protect` (the call's
own variables) may not be assigned. -/
-- @tg: implements:: [[openspec:elpi-typechecker#Mode declarations]]
def unifyMatch (s : Store) (protect : Nat) (a b : Term) (d : Nat) : Option Store :=
  Unify.loop (max protect s.protect) s [(a, b, d)]

end Elpi
