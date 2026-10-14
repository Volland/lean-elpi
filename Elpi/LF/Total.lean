import Elpi.LF.Export

/-!
# LF totality checking

`#total <order> (<family> <args>)` is checked by mode correctness, world regularity, input
coverage, output coverage and termination. The checks are diagnostics outside the trust base;
a claim that passes can additionally be turned into a Lean theorem, which only counts when the
kernel accepts it (see `totalTheorem`).
-/

-- @lat: [[components#LF modes and totality]]

namespace Elpi.LF

/-- First-order patterns over the inputs of a family. -/
inductive Pat where
  | var (n : String)
  | con (c : String) (args : Array Pat)
  deriving Inhabited, BEq

partial def Pat.show : Pat → String
  | .var n => n
  | .con c #[] => c
  | .con c as => c ++ " " ++ " ".intercalate (as.toList.map fun a =>
      match a with | .con _ #[] | .var _ => a.show | _ => "(" ++ a.show ++ ")")

/-- A clause term as a pattern; binders and applications of variables become wildcards. -/
partial def termPat (syms : Symbols) (names : Array String) : Term → Pat
  | .bound l => if h : l < names.size then .var names[l] else .var "_"
  | .const c => .con (syms.name c) #[]
  | .app (.const c) as => .con (syms.name c) (as.map (termPat syms names))
  | _ => .var "_"

/-- Does clause pattern `cp` match goal pattern `gp`, extending the substitution `s`? -/
partial def matchPat (cp gp : Pat) (s : List (String × Pat)) : Option (List (String × Pat)) :=
  match cp, gp with
  | .var x, g =>
    if x == "_" then some s else
    match s.lookup x with
    | some g' => if g' == g then some s else none
    | none => some ((x, g) :: s)
  | .con c as, .con d bs =>
    if c != d || as.size != bs.size then none else
    (List.range as.size).foldlM (fun s i => matchPat as[i]! bs[i]! s) s
  | .con .., .var _ => none

/-- A goal variable that must be split for `cp` to match, if any. -/
partial def splitVar (cp gp : Pat) : Option String :=
  match cp, gp with
  | .con .., .var v => some v
  | .con c as, .con d bs =>
    if c != d || as.size != bs.size then none
    else (List.range as.size).findSome? fun i => splitVar as[i]! bs[i]!
  | _, _ => none

partial def Pat.subst (v : String) (r : Pat) : Pat → Pat
  | .var x => if x == v then r else .var x
  | .con c as => .con c (as.map (Pat.subst v r))

/-- The clauses of a family with the patterns of their input positions. -/
structure ClauseInfo where
  name : String
  names : Array String
  binders : Array (String × LFTy)
  head : Array Term
  ins : Array Pat

def clauseInfos (sig : LFSig) (syms : Symbols) (fam : String) (inputs : Array Nat) : Array ClauseInfo :=
  sig.order.filterMap fun c =>
    match sig.consts[c]? with
    | some t =>
      if t.target == some fam then
        let (binders, head) := peelPi t
        let names := (binders.toList.zipIdx.map fun ((n, _), i) => if n == "_" then s!"V{i}" else n).toArray
        match head with
        | .atom _ hargs =>
          some { name := c, names, binders, head := hargs
                 ins := inputs.map fun i => termPat syms names hargs[i]! }
        | _ => none
      else none
    | none => none

/-- Constructors of a syntax family with the families of their arguments. -/
def ctorsOf (sig : LFSig) (fam : String) : Array (String × Array String) :=
  sig.order.filterMap fun c =>
    match sig.consts[c]? with
    | some t => if t.target == some fam then
        some (c, (peelPi t).1.map fun (_, d) => match d with | .atom g _ => g | _ => "")
      else none
    | none => none

/-- Report of one totality check. -/
inductive TotalResult where
  | ok (summary : String)
  | failed (msg : String)

/-- Input coverage: the first uncovered case, shown as a call. -/
partial def uncovered (sig : LFSig) (cls : Array ClauseInfo) (goal : Array Pat)
    (tys : List (String × String)) (fuel : Nat) : Option (Array Pat) :=
  match fuel with
  | 0 => some goal
  | fuel + 1 =>
    if cls.any fun c => (List.range goal.size).foldlM (fun s i => matchPat c.ins[i]! goal[i]! s) [] |>.isSome then none
    else
      -- find a variable that some clause needs split
      let split? := cls.findSome? fun c =>
        (List.range goal.size).findSome? fun i => splitVar c.ins[i]! goal[i]!
      match split? with
      | none => some goal
      | some v =>
        match tys.lookup v with
        | none => some goal
        | some fam =>
          let ctors := ctorsOf sig fam
          if ctors.isEmpty then some goal else
          ctors.findSome? fun (c, fields) =>
            let fresh := fields.toList.zipIdx.map fun (g, i) => (s!"{v}{i + 1}", g)
            let r := Pat.con c (fresh.toArray.map fun (n, _) => Pat.var n)
            uncovered sig cls (goal.map (Pat.subst v r)) (fresh ++ tys) fuel

/-- Is `t` a proper subterm of `h` (higher-order subterms count: `E x ≺ lam T E`)? -/
partial def properSub (t h : Term) : Bool :=
  let subs : Term → List Term
    | .app _ as => as.toList
    | .lam b => [b]
    | _ => []
  let rec contains (x y : Term) : Bool := x == y || (subs y).any (contains x)
  let tt := match t with
    | .app (.bound v) _ => Term.bound v
    | t => t
  (subs h).any fun s => contains t s || contains tt s

/-- Check a `#total` declaration. -/
-- @tg: implements:: [[openspec:elpi-lf#Totality checking]]
def checkTotal (sig : LFSig) (td : TotalDecl) : TotalResult := Id.run do
  let syms := sig.order.foldl (fun (sy : Symbols) n => (sy.intern n).2) Symbols.initial
  let f := td.fam
  let some md := sig.modes[f]? | return .failed s!"{f} has no #mode declaration"
  let merrs := (checkModes sig).filter fun e =>
    (sig.consts[e.clause]?.bind (·.target)) == some f
  unless merrs.isEmpty do return .failed ("mode checking failed: " ++ merrs[0]!.toString)
  let some (kind, _) := sig.families[f]? | return .failed s!"unknown family {f}"
  let argNames := sig.totalArgs.getD f #[]
  let ins := (List.range md.modes.size).filter (fun i => md.modes[i]!.1) |>.toArray
  let outs := (List.range md.modes.size).filter (fun i => !md.modes[i]!.1) |>.toArray
  let cls := clauseInfos sig syms f ins
  -- world regularity: the hypothetical premises of `f` extend the context by declared blocks
  if let some bs := sig.worlds[f]? then
    for c in sig.order do
      if let some t := sig.consts[c]? then
        if t.target == some f then
          for (_, d) in (peelPi t).1 do
            if let .pi _ (.atom s _) (.pi _ (.atom h _) _) := d then
              let ok := bs.any fun b => match sig.blocks[b]? with
                | some blk => blk.entries.map (fun e => match e.2 with | .atom g _ => g | _ => "") == #[s, h]
                | none => false
              unless ok do
                return .failed s!"world check: clause {c} extends the context by {s}, {h}, which is not a declared block of {f}"
  -- input coverage
  let doms := kind.doms
  let tys := ins.toList.map fun i => (md.modes[i]!.2, match doms[i]? with | some (.atom g _) => g | _ => "")
  let goal := ins.map fun i => Pat.var md.modes[i]!.2
  let showCall (g : Array Pat) : String :=
    f ++ (List.range md.modes.size).foldl (fun s i =>
      let p := match ins.toList.idxOf? i with
        | some k => (g[k]!).show
        | none => md.modes[i]!.2
      s ++ " " ++ (if p.contains ' ' then "(" ++ p ++ ")" else p)) ""
  if let some miss := uncovered sig cls goal tys 8 then
    return .failed s!"input coverage fails: missing case `{showCall miss}`"
  -- output coverage: premise outputs are fresh variables
  for c in cls do
    let mut ground : Array Nat := #[]
    for i in ins do
      for l in levelsOf c.binders.size c.head[i]! #[] do
        unless ground.contains l do ground := ground.push l
    for (_, d) in c.binders do
      if let .atom g pargs := d then
        if let some pmd := sig.modes[g]? then
          for k in [0:pargs.size] do
            if pmd.modes[k]?.map (·.1) == some false then
              match pargs[k]! with
              | .bound l =>
                if ground.contains l then
                  return .failed s!"output coverage fails in clause {c.name}: output {k + 1} of a premise of {g} is not a fresh variable"
                ground := ground.push l
              | _ => return .failed s!"output coverage fails in clause {c.name}: output {k + 1} of a premise of {g} is not a variable"
  -- termination: structural decrease of the designated arguments
  for c in cls do
    for (_, d) in c.binders do
      if let .atom g pargs := d then
        if g == f then
          let mut decreased := false
          for i in td.order do
            let t := pargs[i]!
            let h := c.head[i]!
            if t == h then continue
            decreased := properSub t h
            break
          unless decreased do
            return .failed s!"termination fails: a recursive call in clause {c.name} does not decrease the designated argument"
  let inNames := ins.toList.map fun i => md.modes[i]!.2
  let outNames := outs.toList.map fun i => md.modes[i]!.2
  let ordinal (i : Nat) : String :=
    match i with
    | 0 => "first" | 1 => "second" | 2 => "third" | k => s!"{k + 1}th"
  let ordNames := td.order.toList.map fun i => s!"its {ordinal i} argument ({argNames[i]?.getD "_"})"
  return .ok s!"{f} is total in {" and ".intercalate ordNames}, with inputs {" and ".intercalate inNames} and output {" and ".intercalate outNames}"

/-- The statement `∀ inputs, ∃ outputs, Fam …` of a total family, as Lean source. -/
def totalStatement (p : Plan) (td : TotalDecl) : Except String (String × String) := do
  let f := td.fam
  let some md := p.sig.modes[f]? | throw "no mode"
  let some (kind, _) := p.sig.families[f]? | throw "unknown family"
  if p.ctxual.contains f then throw "a contextual family"
  let doms := kind.doms
  let mut binders := ""
  let mut outs := ""
  for i in [0:md.modes.size] do
    let (isIn, n) := md.modes[i]!
    let ty ← tyLean p "0" doms[i]!
    if isIn then binders := binders ++ s!" («{n}» : {ty})"
    else outs := outs ++ s!" («{n}» : {ty})"
  let call := (List.range md.modes.size).foldl (fun s i => s ++ s!" «{md.modes[i]!.2}»") ""
  return (s!"∀{binders}, ∃{outs}, {p.q f}{call}", f)

/-- A kernel-checkable proof of totality by structural induction on the designated input:
one case per constructor, using the clause that matches it and the induction hypotheses for
its recursive premises. Fails (so no theorem is emitted) outside this shape. -/
-- @tg: implements:: [[openspec:elpi-lf#Totality checking]]
def totalTheorem (sig : LFSig) (td : TotalDecl) : Except String String := do
  let p ← match mkPlan sig with | .ok p => pure p | .error e => throw e.msg
  let syms := sig.order.foldl (fun (sy : Symbols) n => (sy.intern n).2) Symbols.initial
  let f := td.fam
  let some md := sig.modes[f]? | throw "no mode"
  let some (kind, _) := sig.families[f]? | throw "unknown family"
  unless td.order.size == 1 do throw "only a single designated argument is supported"
  let o := td.order[0]!
  let ins := (List.range md.modes.size).filter (fun i => md.modes[i]!.1) |>.toArray
  let outs := (List.range md.modes.size).filter (fun i => !md.modes[i]!.1) |>.toArray
  let some (.atom tf _) := kind.doms[o]? | throw "the designated argument is not of a syntax family"
  let (stmt, _) ← totalStatement p td
  let cls := clauseInfos sig syms f ins
  let ordName := md.modes[o]!.2
  let others := ins.filter (· != o) |>.map fun i => md.modes[i]!.2
  let intros := " ".intercalate (ins.toList.map fun i => s!"«{md.modes[i]!.2}»")
  let gen := if others.isEmpty then "" else " generalizing " ++ " ".intercalate (others.toList.map fun n => s!"«{n}»")
  let mut out := s!"theorem {p.ns}.{f}_total : {stmt} := by\n  intro {intros}\n  induction «{ordName}»{gen} with\n"
  for (c, fields) in ctorsOf sig tf do
    -- the clause for this constructor
    let k := (ins.toList.idxOf o)
    let some cl := cls.find? (fun cl =>
        match (cl.ins[k]? : Option Pat) with
        | some (Pat.con d args) =>
          d == c && args.size == fields.size && args.all (fun a => match a with | .var _ => true | _ => false)
        | _ => false)
      | throw s!"no clause handles the constructor {c}"
    let some (Pat.con _ fieldPats) := (cl.ins[k]? : Option Pat) | throw "internal"
    let fieldNames := fieldPats.map fun | .var n => n | _ => "_"
    -- fields that are again of the designated family get an induction hypothesis
    let recFields := (List.range fields.size).filter (fun i => fields[i]! == tf) |>.map (fieldNames[·]!)
    let ihs := (List.range recFields.length).map fun j => s!"ih{j}"
    let binderNames := " ".intercalate ((fieldNames.toList.map fun n => s!"«{n}»") ++ ihs)
    out := out ++ s!"  | {c} {binderNames} =>\n"
    let env : TEnv :=
      { plan := p, syms, base := cl.binders.size, scope0 := .nat 0,
        inst := fun l => some (.loc (cl.names[l]?.getD "_"), 0, false) }
    let mut proofs : Array String := #[]
    let mut j := 0
    for (_, d) in cl.binders do
      match d with
      | .atom g pargs =>
        if sig.role? g == some .judgment then
          unless g == f do throw s!"clause {cl.name} has a premise of another family"
          let .bound l := pargs[o]! | throw s!"clause {cl.name}: a recursive call on a non-variable"
          let some r := recFields.idxOf? (cl.names[l]?.getD "") |>.filter (· < recFields.length)
            | throw s!"clause {cl.name}: a recursive call not on a field"
          let mut argsSrc := ""
          for i in ins do
            if i != o then argsSrc := argsSrc ++ " " ++ (← (tmL env #[] 0 pargs[i]!)).src
          let mut outNames : Array String := #[]
          for i in outs do
            match pargs[i]! with
            | .bound l => outNames := outNames.push s!"«{cl.names[l]!}»"
            | _ => throw s!"clause {cl.name}: a premise output that is not a variable"
          j := j + 1
          out := out ++ s!"    obtain ⟨{", ".intercalate (outNames.toList ++ [s!"h{j}"])}⟩ := ih{r}{argsSrc}\n"
          proofs := proofs.push s!"h{j}"
      | _ => pure ()
    let mut headOuts : Array String := #[]
    for i in outs do headOuts := headOuts.push (← (tmL env #[] 0 cl.head[i]!)).src
    let app := " ".intercalate ((s!"{p.ns}.{f.capitalize}.{cl.name}") :: proofs.toList)
    out := out ++ s!"    exact ⟨{", ".intercalate (headOuts.toList ++ [app])}⟩\n"
  return out

end Elpi.LF
