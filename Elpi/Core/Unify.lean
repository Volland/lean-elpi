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

/-- Outcome of inverting a term into the scope of a variable. The store is returned in every
case: after `fail` or `delay` it holds partial work, which the caller discards by undoing to its
own checkpoint. (Returning no store would force the caller to keep the old one alive, a second
reference that makes every update copy the store's arrays.) -/
inductive InvR (α : Type) where
  | ok (s : Store) (a : α)
  | fail (s : Store)
  | delay (s : Store)

instance {α : Type} : Inhabited (InvR α) := ⟨.fail default⟩

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
      | none => if l < c.lvl then .ok s t else .fail s
  | .lam b =>
    match inv c s b (k + 1) with
    | .ok s b' => .ok s (.lam b')
    | .fail s => .fail s
    | .delay s => .delay s
  | .app h as =>
    match inv c s h k with
    | .ok s h' =>
      match invArr c s as k with
      | .ok s as' => .ok s (.app h' as')
      | .fail s => .fail s
      | .delay s => .delay s
    | .fail s => .fail s
    | .delay s => .delay s
  | .cvar _ _ => .fail s
  | .uvar y ys =>
    if y == c.x then .fail s
    else
      let ℓy := s.levelOf y
      -- map each argument, remembering which survive
      let m := ys.size
      let rec go (i : Nat) (s : Store) (kept : Array Nat) (outs : Array Term) : Store × Array Nat × Array Term :=
        if h : i < m then
          -- an argument that cannot be expressed is dropped; its partial pruning is undone
          let cp := s.checkpoint
          match inv c s.track ys[i] k with
          | .ok s' a => go (i + 1) (s'.settle cp) (kept.push i) (outs.push a)
          | .fail s' => go (i + 1) (s'.undo cp) kept outs
          | .delay s' => go (i + 1) (s'.undo cp) kept outs
        else (s, kept, outs)
      let (s1, kept, outs) := go 0 s #[] #[]
      if kept.size == m && ℓy ≤ c.lvl then .ok s1 (.uvar y outs)
      else
        -- pruning needs the spine of `y` to be a pattern whenever an argument is dropped
        if kept.size != m && (patternSpine s1 ys (c.d + k)).isNone then .delay s1
        else
          let ℓ' := min ℓy c.lvl
          let (y', s2) := s1.fresh ℓ' (s1.nameOf y)
          -- `y` sees the names that `x` abstracts over when they are in its scope; its
          -- replacement (of a lower level) must receive them as arguments
          let extra := (List.range n).filter fun i => c.spine[i]! ≥ c.lvl && c.spine[i]! < ℓy
          let val := lams m (.uvar y' (kept.map (fun i => Term.bound (ℓy + i)) ++
                                       extra.toArray.map fun i => Term.bound c.spine[i]!))
          let s3 := s2.setAssign y val
          .ok s3 (.uvar y' (outs ++ extra.toArray.map fun i => Term.bound (c.lvl + i)))

partial def invArr (c : InvCtx) (s : Store) (xs : Array Term) (k : Nat) : InvR (Array Term) :=
  let rec go (i : Nat) (s : Store) (acc : Array Term) : InvR (Array Term) :=
    if h : i < xs.size then
      match inv c s xs[i] k with
      | .ok s' a => go (i + 1) s' (acc.push a)
      | .fail s' => .fail s'
      | .delay s' => .delay s'
    else .ok s acc
  go 0 s #[]
end

/-- Result of assigning a flexible term: solved, no solution, or delayed (outside the pattern
fragment). -/
inductive Sol where
  | ok
  | fail
  | delay

/-- Can `x := t` be assigned as it stands? True when `t` (at depth `d`) mentions neither `x` nor
a variable of a scope level above `lvl`, so that inversion would return `t` unchanged for a
variable with an empty spine at its own depth. A read-only scan: no allocation. -/
partial def scanClean (s : Store) (x : UVarId) (lvl : Nat) (t : Term) (d : Nat) : Bool :=
  match t with
  | .const _ | .lit _ | .builtinData _ | .bound _ => true
  | .lam b => scanClean s x lvl b (d + 1)
  | .app h as => scanClean s x lvl h d && as.all (scanClean s x lvl · d)
  | .cvar .. => false
  | .uvar y ys =>
    if y == x then false else
    match s.lookup? y with
    | none => s.levelOf y ≤ lvl && ys.all (scanClean s x lvl · d)
    | some v =>
      if ys.isEmpty then scanClean s x lvl v (s.levelOf y)
      else scanClean s x lvl (s.deref t d) d

/-- Assign `x xs := t` by inversion. The store is always returned: after `fail` it holds partial
work (the caller's attempt is undone as a whole); after `delay` it is as before the call. -/
def solveFlex (s : Store) (x : UVarId) (xs : Array Term) (t : Term) (d : Nat) : Store × Sol :=
  -- first-order case: a variable without a spine at its own depth takes any clean term as is
  if xs.isEmpty && s.levelOf x == d && scanClean s x d t d then (s.setAssign x t, .ok) else
  match patternSpine s xs d with
  | none => (s, .delay)
  | some spine =>
    let c : InvCtx := { x, lvl := s.levelOf x, spine, d }
    let cp := s.checkpoint
    match inv c s.track t 0 with
    | .ok s' t' => ((s'.setAssign x (lams spine.size t')).settle cp, .ok)
    | .fail s' => (s', .fail)
    | .delay s' => (s'.undo cp, .delay)

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

/-- Suspend the problem `a = b` as the goal keyed on its variables (woken on assignment). -/
def delayEqn (s : Store) (a b : Term) (d : Nat) : Store :=
  let keys := collectUVars s b d (collectUVars s a d)
  let (_, cs) := s.cstore.add
    { id := 0, goal := .app (.const eqConst) #[a, b], keys, depth := d, locals := [],
      pred := none }
  { s with cstore := cs }

/-- Consult the hooks (only when pattern unification could not decide the problem). `none`:
no hook decided and the problem should be delayed or failed (`declineFails`); `some r`:
a hook answered, with the equations it asks to solve next (`inl`), or failure/suspension. -/
inductive HookR where
  | decline
  | fail
  | suspend
  | solved (eqs : List (Term × Term))

def runHooks (s : Store) (a b : Term) (d : Nat) : HookR := Id.run do
  for h in s.hooks do
    match h.onStuck (s.deref · d) a b d with
    | .decline => pure ()
    | .fail => return .fail
    | .suspend => return .suspend
    | .solved θ => return .solved (θ.map fun (u, t) => (Term.uvar u #[], t))
  return .decline

/-- Does a clash of `a` and `b` involve an interpreted constant (so hooks get a say)? -/
def interpretedClash (s : Store) (a b : Term) : Bool :=
  !s.hooks.isEmpty &&
  (match headConst a, headConst b with
   | some c, _ => s.interp.contains c.idx
   | _, some c => s.interp.contains c.idx
   | _, _ => false)

/-- The unifier's worklist loop. It always returns the store it reached: after a failure that
store holds the bindings made so far, which the caller undoes through its checkpoint (a
persistent copy would cost a full array copy per attempt). -/
partial def loop (protect : Nat) (s : Store) : List Eqn → Store × Bool
  | [] => (s, true)
  | (a, b, d) :: rest =>
    let a := s.deref a d
    let b := s.deref b d
    -- pattern unification could not decide: ask the hooks, then delay or fail
    match a, b with
    | .uvar x xs, .uvar y ys =>
      if x == y then
        if xs == ys then loop protect s rest
        else
          match patternSpine s xs d, patternSpine s ys d with
          | some px, some py =>
            if px.size != py.size || !assignable protect x then (s, false) else
            let ℓ := s.levelOf x
            let n := px.size
            let kept := (List.range n).filter (fun i => px[i]! == py[i]!) |>.toArray
            let (x', s1) := s.fresh ℓ (s.nameOf x)
            let val := lams n (.uvar x' (kept.map fun i => .bound (ℓ + i)))
            loop protect (s1.setAssign x val) rest
          | _, _ => stuck protect s a b d rest false
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
          let (s', r) := if pickX then solveFlex s x xs b d else solveFlex s y ys a d
          match r with
          | .ok => loop protect s' rest
          | .fail => (s', false)
          | .delay =>
            if assignable protect x || assignable protect y then stuck protect s' a b d rest false
            else (s', false)
        else if !assignable protect x && !assignable protect y then (s, false)
        else stuck protect s a b d rest false
    | .uvar x xs, t =>
      if !assignable protect x then (s, false) else
      let (s', r) := solveFlex s x xs t d
      match r with
      | .ok => loop protect s' rest
      | .fail => (s', false)
      | .delay => stuck protect s' a b d rest false
    | t, .uvar y ys =>
      if !assignable protect y then (s, false) else
      let (s', r) := solveFlex s y ys t d
      match r with
      | .ok => loop protect s' rest
      | .fail => (s', false)
      | .delay => stuck protect s' a b d rest false
    | .lam x, .lam y => loop protect s ((x, y, d + 1) :: rest)
    | .lam x, t => loop protect s ((x, etaApp t d, d + 1) :: rest)
    | t, .lam y => loop protect s ((etaApp t d, y, d + 1) :: rest)
    | .const c, .const c' => if c == c' then loop protect s rest else clashed protect s a b d rest
    | .bound l, .bound l' => if l == l' then loop protect s rest else (s, false)
    | .lit l, .lit l' => if l == l' then loop protect s rest else (s, false)
    | .builtinData o, .builtinData o' => if o == o' then loop protect s rest else (s, false)
    | .app h as, .app h' as' =>
      if as.size != as'.size then clashed protect s a b d rest else
      let hOk :=
        match h, h' with
        | .const c, .const c' => c == c'
        | .bound l, .bound l' => l == l'
        | _, _ => false
      if !hOk then clashed protect s a b d rest else
      loop protect s (zipEqns as as' d rest)
    | _, _ => clashed protect s a b d rest
where
  zipEqns (as as' : Array Term) (d : Nat) (rest : List Eqn) : List Eqn :=
    let rec go (i : Nat) (acc : List Eqn) : List Eqn :=
      if i = 0 then acc else go (i - 1) ((as[i - 1]!, as'[i - 1]!, d) :: acc)
    go (min as.size as'.size) rest
  /-- A rigid clash fails, unless the hooks interpret the constants involved. -/
  clashed (protect : Nat) (s : Store) (a b : Term) (d : Nat) (rest : List Eqn) : Store × Bool :=
    if interpretedClash s a b then hooked protect s a b d rest true else (s, false)
  /-- Pattern unification is stuck: hooks first, then delay (or fail when `declineFails`). -/
  stuck (protect : Nat) (s : Store) (a b : Term) (d : Nat) (rest : List Eqn) (declineFails : Bool) :
      Store × Bool :=
    hooked protect s a b d rest declineFails
  hooked (protect : Nat) (s : Store) (a b : Term) (d : Nat) (rest : List Eqn)
      (declineFails : Bool) : Store × Bool :=
    match runHooks s a b d with
    | .decline => if declineFails then (s, false) else loop protect (delayEqn s a b d) rest
    | .fail => (s, false)
    | .suspend => loop protect (delayEqn s a b d) rest
    | .solved eqs => loop protect s (eqs.map (fun (p, q) => (p, q, d)) ++ rest)

end Unify

/-- Unify `a` and `b` at depth `d`, returning the store reached and whether it succeeded. After a
failure the store holds partial bindings: undo them with the `Store.checkpoint` taken before
the call, with the store in `Store.track` mode. This is the allocation-free form the machine
uses; `unify` below is the persistent-style convenience. -/
def unifyRaw (s : Store) (a b : Term) (d : Nat) : Store × Bool :=
  Unify.loop s.protect s [(a, b, d)]

/-- Match-mode `unifyRaw` for input arguments: variables with an index below `protect` (the
call's own variables) may not be assigned. -/
def unifyMatchRaw (s : Store) (protect : Nat) (a b : Term) (d : Nat) : Store × Bool :=
  Unify.loop (max protect s.protect) s [(a, b, d)]

/-- Unify `a` and `b` at depth `d`; problems outside the pattern fragment are suspended
as constraints in `Store.cstore`, after the registered hooks (if any) were consulted.
Variables below `Store.protect` are frozen (CHR matching and guards). The argument store is
left intact. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Higher-order pattern unification]]
def unify (s : Store) (a b : Term) (d : Nat) : Option Store :=
  let m := s.checkpoint
  let (s', ok) := unifyRaw s.track a b d
  if ok then some (s'.settle m) else none

/-- Match mode for input arguments: variables with an index below `protect` (the call's
own variables) may not be assigned. -/
-- @tg: implements:: [[openspec:elpi-typechecker#Mode declarations]]
def unifyMatch (s : Store) (protect : Nat) (a b : Term) (d : Nat) : Option Store :=
  let m := s.checkpoint
  let (s', ok) := unifyMatchRaw s.track protect a b d
  if ok then some (s'.settle m) else none

end Elpi
