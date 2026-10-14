import Elpi.LF.Mode

/-!
# Lean export of LF signatures

A signature in the exportable fragment becomes Lean declarations: syntax families are
inductives in `Type` (indexed by a scope when they have binders), judgment families are
inductives in `Prop` (indexed by a context when they have hypothetical premises), and every
object constant is one constructor. The same translation turns recorded proof terms into
fully explicit constructor applications (`LExp`), which the Lean side hands to the kernel.
-/

-- @lat: [[components#LF export]]

namespace Elpi.LF

/-! ### Lean expressions of the export language -/

/-- A fully explicit application of an exported constant (implicit arguments included). -/
inductive LExp where
  | app (c : String) (args : Array LExp)
  | nat (n : Nat)
  | loc (name : String)
  deriving Inhabited, BEq

partial def LExp.src : LExp → String
  | .app c as => "(@" ++ c ++ (as.foldl (fun s a => s ++ " " ++ a.src) "") ++ ")"
  | .nat n => toString n
  | .loc n => "«" ++ n ++ "»"

/-! ### The export plan -/

structure Plan where
  sig : LFSig
  ns : String
  /-- Syntax families whose objects have binders (indexed by a scope). -/
  withVars : Std.HashSet String := {}
  /-- Judgment families indexed by a context. -/
  ctxual : Std.HashSet String := {}
  /-- The assumption family and the types of its arguments after the scope variable. -/
  hyp : Option (String × Array LFTy) := none

def Plan.hasCtx (p : Plan) : Bool := p.hyp.isSome

def LFSig.exportNs (sig : LFSig) : String := sig.name.capitalize

def Plan.q (p : Plan) (n : String) : String := p.ns ++ "." ++ n.capitalize
def Plan.qc (p : Plan) (fam c : String) : String := p.ns ++ "." ++ fam.capitalize ++ "." ++ c

/-- Binders and result of a Π telescope. -/
partial def peelPi (t : LFTy) : Array (String × LFTy) × LFTy :=
  let rec go (t : LFTy) (acc : Array (String × LFTy)) :=
    match t with
    | .pi n d c => go c (acc.push (n, d))
    | t => (acc, t)
  go t #[]

def LFKind.doms (k : LFKind) : Array LFTy :=
  let rec go : LFKind → Array LFTy → Array LFTy
    | .type, acc => acc
    | .pi _ d c, acc => go c (acc.push d)
  go k #[]

/-- Number of arrows of a binder-style type `F → … → F`, if it is one. -/
def arrowsOf (f : String) : LFTy → Option Nat
  | .atom g #[] => if g == f then some 0 else none
  | .pi _ (.atom g #[]) c => if g == f then (arrowsOf f c).map (· + 1) else none
  | _ => none

def Plan.isSyn (p : Plan) (f : String) : Bool := p.sig.role? f == some .syn

/-- Analyse a signature; an `Except` naming the offending declaration if it is outside the
exportable fragment. -/
-- @tg: implements:: [[openspec:elpi-lf#Lean inductive export]]
def mkPlan (sig : LFSig) : Except LFError Plan := do
  let mut p : Plan := { sig, ns := sig.exportNs }
  let bad (c : String) (msg : String) : LFError :=
    { decl := c, pos := (sig.positions[c]?).getD default, msg := s!"outside the exportable fragment: {msg}" }
  -- syntax families
  for c in sig.order do
    let some t := sig.consts[c]? | continue
    if sig.bridges.contains c then continue
    let some f := t.target | continue
    unless p.isSyn f do continue
    unless sig.implicit.getD c 0 == 0 do throw (bad c "a syntax constructor with implicit arguments")
    let (args, _) := peelPi t
    for (_, d) in args do
      match d with
      | .atom g as =>
        unless p.isSyn g && as.isEmpty do throw (bad c s!"an argument of type {g} that is not a plain syntax type")
      | .pi .. =>
        match arrowsOf f d with
        | some k => if k > 0 then p := { p with withVars := p.withVars.insert f }
        | none => throw (bad c "a binder argument whose domain is not its own syntax family")
      | _ => throw (bad c "an argument of unknown type")
  for c in sig.order do
    let some t := sig.consts[c]? | continue
    if sig.bridges.contains c then continue
    let some f := t.target | continue
    unless p.isSyn f do continue
    for (_, d) in (peelPi t).1 do
      if let .atom g _ := d then
        if g != f && p.withVars.contains g then throw (bad c s!"an argument of the withVars family {g}")
  -- judgment families: indices must be plain syntax; withVars indices make the family contextual
  for f in sig.order do
    let some (k, role) := sig.families[f]? | continue
    unless role == .judgment do continue
    for d in k.doms do
      match d with
      | .atom g #[] =>
        unless p.isSyn g do throw (bad f s!"an index of type {g}, which is not a syntax family")
        if p.withVars.contains g then p := { p with ctxual := p.ctxual.insert f }
      | _ => throw (bad f "an index that is not a plain syntax type")
  -- clauses: hypothetical premises fix the assumption family
  for c in sig.order do
    let some t := sig.consts[c]? | continue
    let some f := t.target | continue
    if p.isSyn f then continue
    let impl := sig.implicit.getD c 0
    let (binders, _) := peelPi t
    for i in [impl:binders.size] do
      match binders[i]!.2 with
      | .atom g _ =>
        unless sig.role? g == some .judgment do throw (bad c "a judgment constructor with a non-judgment argument")
      | .pi _ (.atom s #[]) (.pi _ (.atom h hargs) _) =>
        unless p.withVars.contains s do throw (bad c "a hypothetical premise over a family without binders")
        let some (hk, _) := sig.families[h]? | throw (bad c "an unknown hypothesis family")
        let doms := hk.doms
        unless doms.size == hargs.size && doms.size ≥ 1 && doms[0]! == .atom s #[] do
          throw (bad c "a hypothesis that is not atomic over the bound variable")
        let ps := doms.extract 1 doms.size
        match p.hyp with
        | none => p := { p with hyp := some (h, ps) }
        | some (h', ps') => unless h == h' && ps == ps' do throw (bad c "hypotheses of two different families")
        p := { p with ctxual := (p.ctxual.insert f).insert h }
      | _ => throw (bad c "a premise that is neither atomic nor a simple hypothetical")
  return p

/-! ### Translating objects -/

/-- Translation environment for the objects of one clause. -/
structure TEnv where
  plan : Plan
  syms : Symbols
  /-- Number of clause-level binders; levels below it are clause variables. -/
  base : Nat
  /-- The scope index `n` of the clause. -/
  scope0 : LExp
  /-- The value of clause variable `l`, how many binder arguments its type has, and whether
  its type is a withVars syntax family. -/
  inst : Nat → Option (LExp × Nat × Bool)

def scopeAt (n0 : LExp) (k : Nat) : LExp :=
  if k == 0 then n0 else match n0 with
    | .nat m => .nat (m + k)
    | e => (List.range k).foldl (fun acc _ => LExp.app "Nat.succ" #[acc]) e

/-- A scope variable introduced while translating: its level and family. -/
abbrev Eig := Array (Nat × String)

/-- Translate an LF object of syntax. `depth` = number of binders in scope. -/
partial def tmL (env : TEnv) (eig : Eig) (depth : Nat) (t : Term) : Except String LExp := do
  let p := env.plan
  let sc (j : Nat) := scopeAt env.scope0 j
  let conApp (c : ConstId) (args : Array Term) : Except String LExp := do
    let name := env.syms.name c
    if let some b := p.sig.bridges[name]? then
      -- a bridged function becomes the Lean function itself
      return .app b.leanName (← args.mapM (tmL env eig depth))
    let some ty := p.sig.consts[name]? | throw s!"{name} is not a constant of the signature"
    let some fam := ty.target | throw s!"{name} has no result family"
    let (doms, _) := peelPi ty
    unless doms.size == args.size do throw s!"{name} is not fully applied"
    let mut out : Array LExp := if p.withVars.contains fam then #[sc eig.size] else #[]
    for i in [0:args.size] do
      let k := (arrowsOf fam doms[i]!.2).getD 0
      -- strip `k` binders of the argument
      let mut a := args[i]!
      let mut e := eig
      let mut d := depth
      for _ in [0:k] do
        match a with
        | .lam b => e := e.push (d, fam); d := d + 1; a := b
        | _ => throw s!"an argument of {name} that is not a λ-abstraction where a binder is expected"
      out := out.push (← tmL env e d a)
    return .app (p.qc fam name) out
  match t with
  | .bound l =>
    if l < env.base then
      let some (e, _, scopedVar) := env.inst l | throw s!"unbound variable {l}"
      if scopedVar && !eig.isEmpty then throw "a variable of withVars type used under a binder needs weakening"
      return e
    else
      match eig.findIdx? (·.1 == l) with
      | none => throw "a bound variable that is not a scope variable"
      | some pos =>
        let fam := eig[pos]!.2
        let d := eig.size - 1 - pos
        let mut v := LExp.app (p.ns ++ ".Var.zero") #[sc pos]
        let mut cur := pos + 1
        for _ in [0:d] do
          v := .app (p.ns ++ ".Var.succ") #[sc cur, v]
          cur := cur + 1
        return .app (p.qc fam "var") #[sc eig.size, v]
  | .lit (.int i) => if i ≥ 0 then return .nat i.toNat else throw "a negative numeral"
  | .const c => conApp c #[]
  | .app (.const c) args => conApp c args
  | .app (.bound l) args =>
    if l < env.base then
      let some (e, extra, _) := env.inst l | throw s!"unbound variable {l}"
      unless extra == args.size do throw "a higher-order variable applied to something other than its binders"
      for a in args do
        match a with
        | .bound m => unless eig.any (·.1 == m) do throw "a higher-order variable applied to a non-variable"
        | _ => throw "a higher-order variable applied to a non-variable"
      return e
    else throw "an applied bound variable"
  | _ => throw "an object outside the exportable fragment"

/-! ### Judgments -/

/-- The Lean type of a clause variable of LF type `t`, at scope `n`. -/
def tyLean (p : Plan) (n : String) (t : LFTy) : Except String String :=
  match t with
  | .atom f #[] =>
    if let some b := p.sig.bridges[f]? then .ok b.leanName
    else if p.withVars.contains f then .ok s!"({p.q f} {n})" else .ok (p.q f)
  | .pi .. =>
    match t.target with
    | some f =>
      match arrowsOf f t with
      | some k =>
        let sc := (List.range k).foldl (fun acc _ => s!"(Nat.succ {acc})") n
        .ok s!"({p.q f} {sc})"
      | none => .error "a variable of function type over several families"
    | none => .error "a variable of unknown type"
  | .atom f _ => .ok (p.q f)   -- indexed families as variables are not supported by `tmL`
  | .unk _ => .error "a variable of unknown type"

/-- Context-aware application of a judgment family. -/
def atomL (env : TEnv) (eig : Eig) (depth : Nat) (ctx : LExp) (f : String) (args : Array Term) :
    Except String LExp := do
  let p := env.plan
  let mut out : Array LExp := #[]
  if p.ctxual.contains f then out := #[scopeAt env.scope0 eig.size, ctx]
  for a in args do out := out.push (← tmL env eig depth a)
  return .app (p.q f) out

/-- Extend the context by one hypothetical premise; returns the new context and eigenvar. -/
def snocL (env : TEnv) (eig : Eig) (depth : Nat) (ctx : LExp) (hargs : Array Term) :
    Except String LExp := do
  let p := env.plan
  let mut out : Array LExp := #[scopeAt env.scope0 eig.size, ctx]
  for a in hargs.extract 1 hargs.size do out := out.push (← tmL env eig depth a)
  return .app (p.ns ++ ".Ctx.snoc") out

/-- A premise or hypothetical premise as a Lean type; `ctx` is the current context. -/
partial def goalL (env : TEnv) (eig : Eig) (depth : Nat) (ctx : LExp) : LFTy → Except String LExp
  | .atom f args => atomL env eig depth ctx f args
  | .pi _ (.atom s #[]) (.pi _ (.atom _ hargs) goal) => do
    let ctx' ← snocL env eig depth ctx hargs
    goalL env (eig.push (depth, s)) (depth + 2) ctx' goal
  | _ => throw "a premise that is neither atomic nor a simple hypothetical"

/-- How a binder of a constructor's Π telescope is used. -/
inductive BKind where
  | var
  | prem
  deriving BEq, Inhabited

/-- The binder kinds of a constant's telescope. -/
def binderKinds (sig : LFSig) (t : LFTy) : Array BKind :=
  (peelPi t).1.map fun (_, d) =>
    match d with
    | .atom g _ => if sig.role? g == some .judgment then .prem else .var
    | .pi .. => if (arrowsOf (d.target.getD "") d).isSome then .var else .prem
    | _ => .var

/-- Instances of clause variables as locals named after their binders. -/
def localInst (p : Plan) (binders : Array (String × LFTy)) (kinds : Array BKind) :
    Nat → Option (LExp × Nat × Bool) := fun l =>
  match binders[l]?, kinds[l]? with
  | some (n, d), some .var =>
    let extra := match d with
      | .pi .. => (arrowsOf (d.target.getD "") d).getD 0
      | _ => 0
    let sv := match d with
      | .atom g _ => p.withVars.contains g
      | _ => false
    some (.loc (varName n l), extra, sv)
  | _, _ => none
where
  varName (n : String) (l : Nat) : String := if n == "_" then s!"a{l}" else n

/-- The constructor declaration of a constant of a judgment family. -/
def judgmentCtor (p : Plan) (syms : Symbols) (c : String) (ty : LFTy) : Except String String := do
  let some j := ty.target | throw "no result family"
  let impl := p.sig.implicit.getD c 0
  let (binders, head) := peelPi ty
  let kinds := binderKinds p.sig ty
  let ctxual := p.ctxual.contains j
  let mut src := s!"  | {c}"
  let n0 : LExp := .loc "n"
  if ctxual then src := src ++ s!" \{n : Nat} \{«Γ» : {p.ns}.Ctx n}"
  for i in [0:binders.size] do
    if kinds[i]! == .var then
      let (nm, d) := binders[i]!
      let ty ← tyLean p "n" d
      let nm := if nm == "_" then s!"a{i}" else nm
      src := src ++ (if i < impl then s!" \{«{nm}» : {ty}}" else s!" («{nm}» : {ty})")
  let mut premises : Array String := #[]
  for i in [0:binders.size] do
    if kinds[i]! == .prem then
      let env : TEnv := { plan := p, syms, base := i, scope0 := n0, inst := localInst p binders kinds }
      premises := premises.push (← goalL env #[] i (.loc "Γ") binders[i]!.2).src
  let env : TEnv := { plan := p, syms, base := binders.size, scope0 := n0, inst := localInst p binders kinds }
  let .atom hf hargs := head | throw "no head"
  let h ← atomL env #[] binders.size (.loc "Γ") hf hargs
  return src ++ " : " ++ " → ".intercalate (premises.toList ++ [h.src])

/-- Syntax families in dependency order; a cycle is an error. -/
def synOrder (p : Plan) : Except String (Array String) := do
  let sig := p.sig
  let fams := sig.order.filter fun f => p.isSyn f && sig.families.contains f && !sig.bridges.contains f
  let mut out : Array String := #[]
  let mut fuel := fams.size * fams.size + 1
  let mut pending := fams
  while !pending.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let mut rest := #[]
    for f in pending do
      let deps : Array String := sig.order.foldl (init := #[]) fun acc c =>
        match sig.consts[c]? with
        | some t =>
          if t.target == some f then
            (peelPi t).1.foldl (init := acc) fun a (_, d) =>
              match d with | .atom g _ => if g != f then a.push g else a | _ => a
          else acc
        | none => acc
      if deps.all out.contains then out := out.push f else rest := rest.push f
    pending := rest
  unless pending.isEmpty do throw s!"syntax families {pending.toList} depend on each other"
  return out

/-- The constructor of a syntax family. -/
def syntaxCtor (p : Plan) (c : String) (ty : LFTy) : Except String String := do
  let some f := ty.target | throw "no result family"
  let isSc := p.withVars.contains f
  let (binders, _) := peelPi ty
  let mut args : Array String := #[]
  for (_, d) in binders do
    match d with
    | .atom g _ => args := args.push (if p.withVars.contains g then s!"{p.q g} n" else p.q g)
    | .pi .. =>
      let k := (arrowsOf f d).getD 0
      let sc := (List.range k).foldl (fun acc _ => s!"(Nat.succ {acc})") "n"
      args := args.push s!"{p.q f} {sc}"
    | _ => throw "unknown argument type"
  let res := if isSc then s!"{p.q f} n" else p.q f
  let ns := if isSc then " {n : Nat}" else ""
  return s!"  | {c}{ns} : " ++ " → ".intercalate (args.toList ++ [res])

def wrapErr {α : Type} (sig : LFSig) (c : String) (r : Except String α) : Except LFError α :=
  match r with
  | .ok s => .ok s
  | .error m => .error { decl := c, pos := (sig.positions[c]?).getD default,
                         msg := s!"outside the exportable fragment: {m}" }

/-- The Lean source of an exportable signature. -/
-- @tg: implements:: [[openspec:elpi-lf#Lean inductive export]]
def exportSource (sig : LFSig) : Except LFError String := do
  let p ← mkPlan sig
  let syms := sig.order.foldl (fun sy n => (sy.intern n).2) Symbols.initial
  let wrap {α : Type} (c : String) (r : Except String α) : Except LFError α := wrapErr sig c r
  let mut out := s!"namespace {p.ns}\n"
  if !p.withVars.isEmpty then
    out := out ++ "inductive Var : Nat → Type where\n  | zero {n : Nat} : Var (Nat.succ n)\n  | succ {n : Nat} : Var n → Var (Nat.succ n)\n"
  for f in ← wrap "" (synOrder p) do
    let isSc := p.withVars.contains f
    out := out ++ s!"inductive {f.capitalize} : {if isSc then "Nat → " else ""}Type where\n"
    if isSc then out := out ++ s!"  | var \{n : Nat} : Var n → {f.capitalize} n\n"
    for c in sig.order do
      if let some t := sig.consts[c]? then
        if t.target == some f && !sig.bridges.contains c then out := out ++ (← wrap c (syntaxCtor p c t)) ++ "\n"
  if let some (h, ps) := p.hyp then
    let pt ← wrap h (ps.foldlM (fun (acc : Array String) d => do return acc.push (← tyLean p "n" d)) #[])
    let pts := pt.foldl (fun s x => s ++ " → " ++ x) ""
    out := out ++ s!"inductive Ctx : Nat → Type where\n  | nil : Ctx 0\n  | snoc \{n : Nat} : Ctx n{pts} → Ctx (Nat.succ n)\n"
    -- lookup of an assumption
    let ps' := pt
    let binders := (List.range ps'.size).foldl (fun s i => s ++ s!" \{p{i} : {ps'[i]!}}") ""
    let names := (List.range ps'.size).foldl (fun s i => s ++ s!" p{i}") ""
    let binders2 := (List.range ps'.size).foldl (fun s i => s ++ s!" \{q{i} : {ps'[i]!}}") ""
    let names2 := (List.range ps'.size).foldl (fun s i => s ++ s!" q{i}") ""
    let tys := ps'.foldl (fun s x => s ++ " → " ++ x) ""
    out := out ++ s!"inductive Lookup : \{n : Nat} → Ctx n → Var n{tys} → Prop where\n"
    out := out ++ s!"  | here \{n : Nat} \{Γ : Ctx n}{binders} : Lookup (Ctx.snoc Γ{names}) Var.zero{names}\n"
    out := out ++ s!"  | there \{n : Nat} \{Γ : Ctx n} \{x : Var n}{binders}{binders2} : Lookup Γ x{names} → Lookup (Ctx.snoc Γ{names2}) (Var.succ x){names}\n"
  -- judgment families
  let jfams := sig.order.filter fun f => sig.role? f == some .judgment && sig.families.contains f
  let multi := jfams.size > 1
  if multi then out := out ++ "mutual\n"
  for f in jfams do
    let some (k, _) := sig.families[f]? | continue
    let ctxual := p.ctxual.contains f
    let mut doms : Array String := #[]
    for d in k.doms do doms := doms.push (← wrap f (tyLean p "n" d))
    let head := if ctxual then s!"\{n : Nat} → {p.ns}.Ctx n" else ""
    let tyStr := " → ".intercalate ((if ctxual then [head] else []) ++ doms.toList ++ ["Prop"])
    out := out ++ s!"inductive {f.capitalize} : {tyStr} where\n"
    if let some (h, ps) := p.hyp then
      if h == f then
        let pt ← wrap h (ps.foldlM (fun (acc : Array String) d => do return acc.push (← tyLean p "n" d)) #[])
        let binders := (List.range pt.size).foldl (fun s i => s ++ s!" \{p{i} : {pt[i]!}}") ""
        let names := (List.range pt.size).foldl (fun s i => s ++ s!" p{i}") ""
        let hq := match k.doms[0]? with | some (.atom sf _) => p.q sf | _ => p.ns
        out := out ++ s!"  | hyp \{n : Nat} \{Γ : Ctx n} \{x : Var n}{binders} : Lookup Γ x{names} → {f.capitalize} Γ ({hq}.var x){names}\n"
    for c in sig.order do
      if let some t := sig.consts[c]? then
        if t.target == some f then out := out ++ (← wrap c (judgmentCtor p syms c t)) ++ "\n"
  if multi then out := out ++ "end\n"
  out := out ++ s!"end {p.ns}\n"
  return out


/-- Evaluate bridged applications on numerals: the conversion the kernel performs by
unfolding, used by the LF re-check to compare types. -/
partial def LExp.normBridge (fns : Std.HashMap String (Nat × (Array Nat → Nat))) : LExp → LExp
  | .app c as =>
    let as := as.map (LExp.normBridge fns)
    match fns[c]? with
    | some (ar, f) =>
      if ar == as.size then
        match as.mapM fun | .nat n => some n | _ => none with
        | some vs => .nat (f vs)
        | none => .app c as
      else .app c as
    | none => .app c as
  | e => e

/-! ### Certificates: proof terms as explicit constructor applications -/

/-- State of the proof-term translation: scope variables, contexts, and assumptions. -/
structure PCtx where
  eig : Eig := #[]
  /-- `ctxs[t]` is the context after `t` assumptions. -/
  ctxs : Array LExp := #[]
  /-- The proof-level of each assumption and its parameters. -/
  hyps : Array (Nat × Array LExp) := #[]

def cmpErr (what : String) (want got : LExp) : String :=
  s!"LF re-check failed: {what} has type {got.src}, but {want.src} was expected"

mutual
/-- Translate a proof term; returns the proof and its conclusion. With `recheck`, the
conclusion of every premise proof is compared with the premise it must prove. -/
partial def proofL (p : Plan) (syms : Symbols) (recheck : Bool) (norm : LExp → LExp) (pc : PCtx) (depth : Nat)
    (t : Term) : Except String (LExp × LExp) := do
  let sc (j : Nat) : LExp := .nat j
  let ctxCur := pc.ctxs.back?.getD (.loc "Γ")
  let (head, args) : Term × Array Term := match t with
    | .app h as => (h, as)
    | t => (t, #[])
  match head with
  | .bound l =>
    -- a use of an assumption
    let some i := pc.hyps.findIdx? (·.1 == l) | throw "a bound variable that is not an assumption"
    let some (hf, _) := p.hyp | throw "assumption without an assumption family"
    let m := pc.hyps.size
    let ps := pc.hyps[i]!.2
    let mkPs (xs : Array LExp) := xs
    let mut w := LExp.app (p.ns ++ ".Lookup.here") (#[sc i, pc.ctxs[i]!] ++ ps)
    let mut x := LExp.app (p.ns ++ ".Var.zero") #[sc i]
    for r in [1:m - i] do
      w := .app (p.ns ++ ".Lookup.there")
        (#[sc (i + r), pc.ctxs[i + r]!, x] ++ ps ++ pc.hyps[i + r]!.2 ++ #[w])
      x := .app (p.ns ++ ".Var.succ") #[sc (i + r), x]
    let some (k, _) := p.sig.families[hf]? | throw "unknown assumption family"
    let sf := match (k.doms[0]? : Option LFTy) with | some (.atom sf _) => sf | _ => ""
    let tmv := LExp.app (p.qc sf "var") #[sc m, x]
    let proof := LExp.app (p.q hf ++ ".hyp") (#[sc m, ctxCur, x] ++ mkPs ps ++ #[w])
    let concl := LExp.app (p.q hf) (#[sc m, ctxCur, tmv] ++ ps)
    return (proof, concl)
  | .const c =>
    let name := syms.name c
    let some ty := p.sig.consts[name]? | throw s!"{name} is not a constant of the signature"
    let some j := ty.target | throw s!"{name} has no result family"
    let (binders, hd) := peelPi ty
    unless binders.size == args.size do throw s!"{name} is applied to {args.size} arguments, expected {binders.size}"
    let kinds := binderKinds p.sig ty
    let ctxual := p.ctxual.contains j
    let mut insts : Array (Option (LExp × Nat × Bool)) := #[]
    let mut out : Array LExp := if ctxual then #[sc pc.eig.size, ctxCur] else #[]
    for i in [0:binders.size] do
      let (_, dom) := binders[i]!
      let envI : TEnv :=
        { plan := p, syms, base := i, scope0 := sc pc.eig.size, inst := fun l => (insts[l]?).bind id }
      if kinds[i]! == .var then
        let fam := dom.target.getD ""
        let k := (arrowsOf fam dom).getD 0
        let mut a := args[i]!
        let mut e := pc.eig
        let mut d := depth
        for _ in [0:k] do
          match a with
          | .lam b => e := e.push (d, fam); d := d + 1; a := b
          | _ => throw s!"an argument of {name} that is not a λ-abstraction where a binder is expected"
        let envA : TEnv := { envI with scope0 := sc 0, base := 0 }
        let v ← tmL envA e d a
        let sv := match dom with | .atom g _ => p.withVars.contains g | _ => false
        insts := insts.push (some (v, k, sv))
        out := out.push v
      else
        insts := insts.push none
        let expected ← if recheck then (do return some (← goalL envI #[] i ctxCur dom)) else pure none
        let (pr, concl) ← premiseProof p syms recheck norm pc depth envI i ctxCur dom args[i]!
        if let some want := expected then
          unless norm want == norm concl do throw (cmpErr s!"the argument {i + 1} of {name}" want concl)
        out := out.push pr
    let envH : TEnv :=
      { plan := p, syms, base := binders.size, scope0 := sc pc.eig.size, inst := fun l => (insts[l]?).bind id }
    let .atom hf hargs := hd | throw "no head"
    let concl ← atomL envH #[] binders.size ctxCur hf hargs
    return (.app (p.qc j name) out, concl)
  | _ => throw "a proof term with an unsupported head"

/-- The proof of one premise of a clause: plain, or under a hypothetical binder. -/
partial def premiseProof (p : Plan) (syms : Symbols) (recheck : Bool) (norm : LExp → LExp) (pc : PCtx) (depth : Nat)
    (envI : TEnv) (i : Nat) (ctxCur : LExp) (dom : LFTy) (arg : Term) :
    Except String (LExp × LExp) := do
  match dom with
  | .atom .. => proofL p syms recheck norm pc depth arg
  | .pi _ (.atom s #[]) (.pi _ (.atom _ hargs) goal) =>
    match arg with
    | .lam (.lam body) =>
      let mut ps : Array LExp := #[]
      for a in hargs.extract 1 hargs.size do ps := ps.push (← tmL envI #[] i a)
      let m := pc.eig.size
      let ctx' := LExp.app (p.ns ++ ".Ctx.snoc") (#[.nat m, ctxCur] ++ ps)
      let pc' : PCtx :=
        { eig := pc.eig.push (depth, s), ctxs := pc.ctxs.push ctx', hyps := pc.hyps.push (depth + 1, ps) }
      premiseProof p syms recheck norm pc' (depth + 2) envI i ctx' goal body
    | _ => throw "a hypothetical premise whose proof is not a pair of abstractions"
  | _ => throw "unsupported premise"

end

/-- Certificate of a query answer: the statement and its proof. -/
-- @tg: implements:: [[openspec:elpi-lf#Kernel-checked certificates]]
def certificate (sig : LFSig) (syms : Symbols) (fam : String) (args : Array Term) (proof : Term)
    (recheck : Bool := true) (norm : LExp → LExp := id) : Except LFError (LExp × LExp) := do
  let p ← mkPlan sig
  let err (m : String) : LFError := { decl := fam, pos := default, msg := m }
  let ctx0 := LExp.app (p.ns ++ ".Ctx.nil") #[]
  let pc : PCtx := { ctxs := if p.hasCtx then #[ctx0] else #[] }
  let env0 : TEnv := { plan := p, syms, base := 0, scope0 := .nat 0, inst := fun _ => none }
  let stmt ← match atomL env0 #[] 0 ctx0 fam args with
    | .ok s => pure s
    | .error m => throw (err s!"the instantiated query cannot be translated: {m}")
  let (pr, concl) ← match proofL p syms recheck norm pc 0 proof with
    | .ok r => pure r
    | .error m => throw (err m)
  if recheck && norm stmt != norm concl then throw (err (cmpErr "the proof term" stmt concl))
  return (stmt, pr)

end Elpi.LF
