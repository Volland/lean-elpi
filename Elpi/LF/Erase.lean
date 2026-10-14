import Elpi.LF.ProofTerm

/-!
# Erasure

The plain view of an LF signature: a family becomes a `kind` (syntax) or a predicate type
(judgment), a constant a constructor or clause of the simple type obtained by erasing the
dependencies, `pi x:A\` becomes `pi x\` and a hypothesis becomes `=>`. The result is valid
ELPI 1.18 source, so plain files can call LF predicates and the oracle can run the same
program.
-/

-- @lat: [[components#LF proof terms]]

namespace Elpi.LF

/-- ELPI source for a core term: `names` for the outer Π binders (levels below `base`), `x<i>`
for inner binders, constants named by the signature's symbols. -/
partial def eraseTermS (syms : Symbols) (names : Array String) (base : Nat) (t : Term)
    (depth : Nat) (top : Bool) : String :=
  let wrap (s : String) := if top then s else "(" ++ s ++ ")"
  match t with
  | .bound l => if l < base then names[l]! else s!"x{l - base}"
  | .const c => syms.name c
  | .app h as =>
    wrap (eraseTermS syms names base h depth false ++ " " ++
      " ".intercalate (as.toList.map fun a => eraseTermS syms names base a depth false))
  | .lam b => wrap s!"x{depth}\\ {eraseTermS syms names base b (depth + 1) true}"
  | _ => "_"

/-- The simple type of an LF type: erase dependencies. -/
partial def eraseTy (sig : LFSig) : LFTy → String
  | .atom f _ => f
  | .pi _ d c => s!"({eraseTy sig d} -> {eraseTy sig c})"
  | .unk _ => "_"

/-- The top-level type text of a simply typed signature entry (`a -> b -> c`). -/
partial def eraseArrow (sig : LFSig) (t : LFTy) : String :=
  match t with
  | .pi _ d c =>
    let ds := match d with | .pi .. => "(" ++ eraseArrow sig d ++ ")" | _ => eraseTy sig d
    ds ++ " -> " ++ eraseArrow sig c
  | .atom f _ => f
  | .unk _ => "_"

/-- The text of an erased premise (a goal), with `base` = its position in the telescope. -/
partial def erasePrem (sig : LFSig) (syms : Symbols) (names : Array String) (j : Nat)
    (t : LFTy) (depth : Nat) : String :=
  match t with
  | .pi _ dom cod =>
    let y := s!"x{depth}"
    match dom with
    | .atom f bargs =>
      if sig.role? f == some .judgment then
        let h := f ++ (bargs.foldl (fun acc a => acc ++ " " ++ eraseTermS syms names j a (depth + 1) false) "")
        s!"({h}) => {erasePrem sig syms names j cod (depth + 1)}"
      else s!"pi {y}\\ {erasePrem sig syms names j cod (depth + 1)}"
    | _ => s!"pi {y}\\ {erasePrem sig syms names j cod (depth + 1)}"
  | .atom f args =>
    f ++ (args.foldl (fun acc a => acc ++ " " ++ eraseTermS syms names j a depth false) "")
  | .unk _ => "_"

/-- The erased clause of a judgment constant. -/
def eraseClause (sig : LFSig) (syms : Symbols) (c : String) (t : LFTy) : String := Id.run do
  let rec peel (t : LFTy) (acc : Array (String × LFTy)) : Array (String × LFTy) × LFTy :=
    match t with
    | .pi n d cod => peel cod (acc.push (n, d))
    | t => (acc, t)
  let (binders, head) := peel t #[]
  let names := (binders.toList.zipIdx.map fun ((n, _), i) =>
    if n == "_" then s!"V{i}" else n).toArray
  let .atom fam hargs := head | return s!"% {c}: no head\n"
  let k := binders.size
  let hs := fam ++ (hargs.foldl (fun acc a => acc ++ " " ++ eraseTermS syms names k a 0 false) "")
  let mut goals : Array String := #[]
  for j in (List.range k).reverse do
    let (_, dom) := binders[j]!
    if sig.isJudgmentTy dom then
      goals := goals.push ("(" ++ erasePrem sig syms names j dom 0 ++ ")")
  if goals.isEmpty then return hs ++ ".\n"
  return hs ++ " :- " ++ ", ".intercalate goals.toList ++ ".\n"

/-- The erased signature as ELPI source. -/
-- @tg: implements:: [[openspec:elpi-lf#Interoperation with plain programs]]
def erase (sig : LFSig) : String := Id.run do
  let syms := sig.order.foldl (fun sy n => (sy.intern n).2) Symbols.initial
  let mut out := s!"% erased from the LF signature {sig.name}\n"
  -- kinds and judgment predicate types first
  for n in sig.order do
    if let some (_, role) := sig.families[n]? then
      match role with
      | .syn => out := out ++ s!"kind {n} type.\n"
      | .judgment => pure ()
  for n in sig.order do
    if let some t := sig.consts[n]? then
      if !sig.isJudgmentTy t then
        -- skip the implicit Π's of syntax constants (their types are simple already)
        out := out ++ s!"type {n} {eraseArrow sig (stripImplicit sig n t)}.\n"
  for n in sig.order do
    if let some (k, role) := sig.families[n]? then
      if role == .judgment then
        let rec kdoms : LFKind → List LFTy
          | .type => []
          | .pi _ d c => d :: kdoms c
        out := out ++ s!"type {n} {String.intercalate " -> " ((kdoms k).map (eraseTy sig) ++ ["prop"])}.\n"
  for n in sig.order do
    if let some t := sig.consts[n]? then
      if sig.isJudgmentTy t then
        out := out ++ eraseClause sig syms n t
  return out
where
  stripImplicit (sig : LFSig) (n : String) (t : LFTy) : LFTy :=
    let k := sig.implicit.getD n 0
    let rec go : Nat → LFTy → LFTy
      | 0, t => t
      | k + 1, .pi _ _ c => go k c
      | _, t => t
    go k t

/-- Unit preprocessor for the loader: an `#lf` unit is replaced by its erasure. -/
def preprocessUnit (file src : String) : Except String String :=
  if LFSyntax.isLF file src then
    match loadSource (file.splitOn "/" |>.getLast! |>.replace ".elpi" "") file src with
    | .ok sig => .ok (erase sig)
    | .error e => .error e.toString
  else .ok src

end Elpi.LF
