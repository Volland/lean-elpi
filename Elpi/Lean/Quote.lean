import Lean
import Elpi.Core.Parser
import Elpi.Lean.Reflect

/-!
# Quotations

`{{ t }}` inside ELPI source is a Lean term, elaborated when the source is accumulated, in the
environment and namespace of the accumulation point, and stored reflected. `_` holes become
fresh ELPI variables; an antiquotation `lp:{{X}}` splices the ELPI term `X`: the position is
elaborated as a hole and the hole is then linked to the variable.
-/

-- @lat: [[components#Expr reflection]]

namespace Elpi.Quote

open _root_.Lean Meta Elab Term

/-- A quotation failure: the ELPI position of the quotation and Lean's message. -/
abbrev QErr := Pos × String

/-- Replace each `lp:{{ … }}` by the named hole `?lp_k`; returns the new text and the ELPI
sources of the antiquotations, in order. -/
partial def splitAntiquotes (text : String) (tag : String := "lp") : String × List String :=
  let cs := text.toList.toArray
  let n := cs.size
  let rec go (i : Nat) (acc : String) (srcs : List String) (k : Nat) (fuel : Nat) : String × List String :=
    match fuel with
    | 0 => (acc, srcs.reverse)
    | fuel + 1 =>
      if i ≥ n then (acc, srcs.reverse)
      else if cs[i]! == 'l' && i + 5 < n && cs[i+1]! == 'p' && cs[i+2]! == ':' && cs[i+3]! == '{' && cs[i+4]! == '{' then
        -- find the matching `}}`
        let rec close (j : Nat) (depth : Nat) (f : Nat) : Nat :=
          match f with
          | 0 => j
          | f + 1 =>
            if j + 1 ≥ n then j
            else if cs[j]! == '{' && cs[j+1]! == '{' then close (j + 2) (depth + 1) f
            else if cs[j]! == '}' && cs[j+1]! == '}' then
              if depth == 1 then j else close (j + 2) (depth - 1) f
            else close (j + 1) depth f
        let e := close (i + 5) 1 (n + 1)
        let inner := String.ofList (cs.extract (i + 5) e).toList
        go (e + 2) (acc ++ s!"?{tag}_{k}") (inner :: srcs) (k + 1) fuel
      else go (i + 1) (acc.push cs[i]!) srcs k fuel
  go 0 "" [] 0 (n + 1)

/-- Elaborate one quotation. -/
def elabQuote (text : String) (pos : Pos) : TermElabM (Except QErr STm) := do
  -- hole names are unique per quotation: Lean reuses a `?x` within one elaboration
  let uniq := (← mkFreshId).toString.map fun c => if c.isAlphanum then c else '_'
  let tag := s!"lp{uniq}"
  let (text', srcs) := splitAntiquotes text tag
  -- the antiquoted ELPI terms
  let mut holes : List STm := []
  for s in srcs do
    match Parser.parseQuery pos.file s with
    | .ok t => holes := holes ++ [t]
    | .error e => return .error (pos, s!"in antiquotation: {e.msg}")
  try
    let stx ← match Parser.runParserCategory (← getEnv) `term text' with
      | .ok s => pure s
      | .error m => return .error (pos, m)
    let e ← withSynthesize (postpone := .partial) (elabTerm stx none)
    let e ← instantiateMVars e
    let mvars ← getMVars e
    let mut idx : Std.HashMap MVarId Nat := {}
    let mut extra := holes.length
    for m in mvars do
      let d ← m.getDecl
      let s := d.userName.toString
      match (if s.startsWith (tag ++ "_") then (s.drop (tag.length + 1)).toString.toNat? else none) with
      | some k => idx := idx.insert m k
      | none => idx := idx.insert m extra; extra := extra + 1
    match Reflect.toTermAt { holeOf := fun m => idx[m]? } e 0 with
    | .ok t => return .ok (.term t holes extra pos)
    | .error m => return .error (pos, m)
  catch ex =>
    return .error (pos, ← ex.toMessageData.toString)

/-- Elaborate every quotation of a term; the first failure wins. -/
partial def elabTm : STm → TermElabM (Except QErr STm)
  | .quote text p => elabQuote text p
  | .app f as p => do
    match ← elabTm f with
    | .error e => return .error e
    | .ok f' =>
      let mut out : Array STm := #[]
      for a in as do
        match ← elabTm a with
        | .error e => return .error e
        | .ok a' => out := out.push a'
      return .ok (.app f' out.toList p)
  | .lam x b p => do
    match ← elabTm b with
    | .error e => return .error e
    | .ok b' => return .ok (.lam x b' p)
  | .spill g p => do
    match ← elabTm g with
    | .error e => return .error e
    | .ok g' => return .ok (.spill g' p)
  | t => return .ok t

def elabOpt : Option STm → TermElabM (Except QErr (Option STm))
  | none => return .ok none
  | some t => do
    match ← elabTm t with
    | .ok t' => return .ok (some t')
    | .error e => return .error e

def elabList (ts : List STm) : TermElabM (Except QErr (List STm)) := do
  let mut out : Array STm := #[]
  for t in ts do
    match ← elabTm t with
    | .ok t' => out := out.push t'
    | .error e => return .error e
  return .ok out.toList

/-- Elaborate the quotations of a list of declarations (clauses and CHR rules). -/
-- @tg: implements:: [[openspec:lean-reflection#Quotations]]
partial def elabDecls (ds : List Decl) : TermElabM (Except QErr (List Decl)) := do
  let mut out : Array Decl := #[]
  for d in ds do
    match d with
    | .clause a t p =>
      match ← elabTm t with
      | .error e => return .error e
      | .ok t' => out := out.push (.clause a t' p)
    | .constraint ps rs p =>
      let mut rs' : Array CHRRuleAst := #[]
      for r in rs do
        let .ok kept ← elabList r.kept | return .error (r.pos, "quotation failed")
        let .ok removed ← elabList r.removed | return .error (r.pos, "quotation failed")
        let .ok guard ← elabOpt r.guard | return .error (r.pos, "quotation failed")
        let .ok body ← elabOpt r.body | return .error (r.pos, "quotation failed")
        rs' := rs'.push { r with kept, removed, guard, body }
      out := out.push (.constraint ps rs'.toList p)
    | .ns n inner p =>
      match ← elabDecls inner with
      | .error e => return .error e
      | .ok inner' => out := out.push (.ns n inner' p)
    | d => out := out.push d
  return .ok out.toList

end Elpi.Quote
