import Elpi.LF.Erase

/-!
# LF mode checking

Twelf-style `#mode` declarations are checked as an abstract interpretation over the two values
*ground* and *unknown*: read left to right, every input of a premise must be ground given the
head's inputs and the outputs of earlier premises, and every output of the head must be ground
once all premises have succeeded.
-/

-- @lat: [[components#LF modes and totality]]

namespace Elpi.LF

/-- The Π-bound levels (below `limit`) occurring in a term, with their order of occurrence. -/
partial def levelsOf (limit : Nat) : Term → Array Nat → Array Nat
  | .bound l, acc => if l < limit && !acc.contains l then acc.push l else acc
  | .app h as, acc => as.foldl (fun a t => levelsOf limit t a) (levelsOf limit h acc)
  | .lam b, acc => levelsOf limit b acc
  | _, acc => acc

/-- A mode violation. -/
structure ModeError where
  clause : String
  msg : String
  deriving Inhabited

def ModeError.toString (e : ModeError) : String := s!"clause {e.clause} violates the mode: {e.msg}"

private structure MCtx where
  sig : LFSig
  syms : Symbols
  clause : String
  names : Array String := #[]
  ground : Array Nat := #[]
  errors : Array ModeError := #[]

private def showAtom (c : MCtx) (f : String) (args : Array Term) : String :=
  let n := c.names.size
  f ++ args.foldl (fun acc a => acc ++ " " ++ eraseTermS c.syms c.names n a n false) ""

/-- Check the arguments in input position of an atom are ground. `what` describes the place. -/
private def checkInputs (c : MCtx) (f : String) (args : Array Term) (what : String) : MCtx := Id.run do
  let some md := c.sig.modes[f]? | return c
  let mut c := c
  for i in [0:args.size] do
    if md.modes[i]?.map (·.1) == some true then
      for l in levelsOf c.names.size args[i]! #[] do
        unless c.ground.contains l do
          c := { c with errors := c.errors.push (ModeError.mk c.clause s!"in {what} `{showAtom c f args}`, input argument {i + 1} contains `{c.names[l]!}`, which is not ground") }
  return c

private def addOutputs (c : MCtx) (f : String) (args : Array Term) : MCtx := Id.run do
  let n := c.names.size
  let md? := c.sig.modes[f]?
  let mut g := c.ground
  for i in [0:args.size] do
    let isOut : Bool := match md? with
      | some md => md.modes[i]?.map (·.1) == some false
      | none => true
    if isOut then
      for l in levelsOf n args[i]! #[] do
        unless g.contains l do g := g.push l
  return { c with ground := g }

/-- A premise or hypothetical premise, read as a goal. -/
private partial def goal (c : MCtx) : LFTy → MCtx
  | .atom f args => addOutputs (checkInputs c f args "premise") f args
  | .pi n dom cod =>
    match dom with
    | .atom f args =>
      if c.sig.role? f == some .judgment then
        -- an assumed hypothesis: its inputs must be ground when it is introduced
        let c := checkInputs { c with names := c.names.push n } f args "hypothesis"
        goal c cod
      else
        let c := { c with names := c.names.push n, ground := c.ground.push c.names.size }
        goal c cod
    | _ => goal { c with names := c.names.push n } cod
  | .unk _ => c

/-- Check one clause (a judgment constant) against the mode of its family. -/
def checkClauseMode (sig : LFSig) (syms : Symbols) (name : String) (ty : LFTy) : Array ModeError := Id.run do
  -- split the telescope into binders and the head
  let mut names : Array String := #[]
  let mut prems : Array (Nat × LFTy) := #[]   -- depth at which the premise sits
  let mut cur := ty
  let mut head : Option (String × Array Term) := none
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    match cur with
    | .pi n d c =>
      match d with
      | .atom f _ => if sig.role? f == some .judgment then prems := prems.push (names.size, d)
      | .pi .. => prems := prems.push (names.size, d)
      | _ => pure ()
      names := names.push n
      cur := c
    | .atom f args => head := some (f, args); break
    | .unk _ => break
  let some (hf, hargs) := head | return #[]
  let some md := sig.modes[hf]? | return #[]
  let total := names.size
  -- inputs of the head are ground
  let mut ground : Array Nat := #[]
  for i in [0:hargs.size] do
    if md.modes[i]?.map (·.1) == some true then
      for l in levelsOf total hargs[i]! #[] do
        unless ground.contains l do ground := ground.push l
  let mut c : MCtx := { sig, syms, clause := name, names, ground }
  for (depth, p) in prems do
    -- premises are read at the depth where they occur; the names array is the full one,
    -- but only the levels below `depth` may occur in them
    c := { c with names := names.extract 0 depth }
    c := goal c p
  c := { c with names }
  for i in [0:hargs.size] do
    if md.modes[i]?.map (·.1) == some false then
      for l in levelsOf total hargs[i]! #[] do
        unless c.ground.contains l do
          c := { c with errors := c.errors.push (ModeError.mk name s!"output argument {i + 1} of the head `{showAtom c hf hargs}` contains `{names[l]!}`, which is not ground after the premises") }
  return c.errors

/-- Mode-check every clause of every moded family in a signature. -/
-- @tg: implements:: [[openspec:elpi-lf#Mode checking]]
def checkModes (sig : LFSig) : Array ModeError := Id.run do
  let syms := sig.order.foldl (fun sy n => (sy.intern n).2) Symbols.initial
  let mut errs := #[]
  for c in sig.order do
    if let some t := sig.consts[c]? then
      errs := errs ++ checkClauseMode sig syms c t
  return errs

end Elpi.LF
