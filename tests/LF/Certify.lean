import TestUtil
import Lean
open Elpi TestUtil

private def stlcLp : IO String := do
  return "lf_signature stlc lp%{\n" ++ (← IO.FS.readFile "tests/LF/stlc.elpi") ++ "}%\n"

private def infos (msgs : List (Lean.MessageSeverity × Nat × Nat × String)) : List String :=
  msgs.filterMap fun (s, _, _, t) => if s == .information then some t else none

private def errors (msgs : List (Lean.MessageSeverity × Nat × Nat × String)) : List String :=
  msgs.filterMap fun (s, _, _, t) => if s == .error then some t else none

private def header : String := "import Elpi\nopen Elpi.LFCmd\n"

-- @tg: verifies:: [[openspec:elpi-lf#Lean inductive export#Type family compiles to an inductive family]]
#eval show IO Unit from do
  let src := header ++ (← stlcLp) ++ "lf_export stlc\n#check @Stlc.Of.of_lam\n#check @Stlc.Tm.lam\n#check @Stlc.Tm.var\n#check @Stlc.Tp.arr\n#check @Stlc.Ctx.snoc\n"
  let msgs ← elabSource src
  check (errors msgs).isEmpty s!"errors: {errors msgs}"
  let all := " ".intercalate (infos msgs)
  -- the premise is over the extended context, the conclusion over the original one
  check (hasSub all "Stlc.Of (Γ.snoc T1) E T2") s!"{all}"
  check (hasSub all "Stlc.Of Γ (Stlc.Tm.lam T1 E) (T1.arr T2)") s!"{all}"
  check (hasSub all "Stlc.Tm n.succ") s!"{all}"

-- @tg: verifies:: [[openspec:elpi-lf#Kernel-checked certificates#Derivation is accepted by the Lean kernel]]
#eval show IO Unit from do
  let src := header ++ (← stlcLp) ++ "lf_export stlc\nlf_certify stlc id_typed lp%{ of (lam base x\\ x) (arr base base) }%\n#print id_typed\n#print axioms id_typed\n"
  let msgs ← elabSource src
  check (errors msgs).isEmpty s!"errors: {errors msgs}"
  let all := " ".intercalate (infos msgs)
  check (hasSub all "theorem id_typed : Stlc.Of Stlc.Ctx.nil") s!"{all}"
  check (hasSub all "does not depend on any axioms") s!"{all}"

-- @tg: verifies:: [[openspec:elpi-lf#Kernel-checked certificates#Corrupted certificate is rejected]]
#eval show IO Unit from do
  let corrupt := "open Lean Elab Command Elpi.LF in\nrun_cmd do\n" ++
    "  let some (sig : LFSig) := (match Elpi.LFCmd.getSig (← getEnv) \"stlc\" with | .ok s => some s | .error _ => none) | throwError \"no sig\"\n" ++
    "  let .ok prog := elaborate sig | throwError \"elab\"\n" ++
    "  let [.ok a] := (runQuery sig prog \"of (lam base x\\\\ x) (arr base base)\").take 1 | throwError \"query\"\n" ++
    "  let arrBB := Elpi.Term.app (.const (Elpi.constIdOf \"arr\")) #[Elpi.Term.const (Elpi.constIdOf \"base\"), Elpi.Term.const (Elpi.constIdOf \"base\")]\n" ++
    -- of_lam base (x\\ x) base (x\\ u\\ u)  ↦  of_lam base (x\\ x) (arr base base) (x\\ u\\ u)
    "  let bad := match a.proof with | .app h args => Elpi.Term.app h (args.set! 2 arrBB) | t => t\n" ++
    "  let .atom fam args := a.ty | throwError \"ty\"\n" ++
    "  try\n    liftCoreM (Elpi.LFCmd.certifyProof sig a.syms `bad_cert fam args bad (recheck := false))\n    logError \"ACCEPTED\"\n" ++
    "  catch e => logInfo m!\"REJECTED {e.toMessageData}\"\n#check bad_cert\n"
  let src := header ++ (← stlcLp) ++ "lf_export stlc\n" ++ corrupt
  let msgs ← elabSource src
  let all := " ".intercalate (infos msgs)
  check (hasSub all "REJECTED") s!"{all} / {errors msgs}"
  check (hasSub all "type mismatch") s!"the kernel's error should be reported: {all}"
  check (!(hasSub all "ACCEPTED") && !(errors msgs).any (hasSub · "ACCEPTED")) "the corrupted certificate was accepted"
  check ((errors msgs).any fun e => hasSub e "bad_cert") s!"bad_cert must not exist afterwards: {msgs}"

-- the engine refuses to certify an answer with residual problems
-- @tg: verifies:: [[openspec:elpi-lf#Pattern unification for LF#LF unification stays in the pattern fragment]]
#eval show IO Unit from do
  let sigTxt := (← IO.FS.readFile "tests/LF/stlc.elpi") ++ "c : tm.\np : tm -> type.\np_c : p c.\nq : (tm -> tm) -> type.\nq_c : q F <- p (F (app c c)).\n"
  let src := header ++ "lf_signature s2 lp%{\n" ++ sigTxt ++ "}%\nlf_export s2\nlf_certify s2 residue lp%{ q G }%\n"
  let msgs ← elabSource src
  check ((errors msgs).any fun e => hasSub e "residual") s!"{errors msgs}"

-- @tg: verifies:: [[openspec:elpi-lf#Interoperation with plain programs#LF predicate is callable from a plain program]]
#eval show IO Unit from do
  let path ← IO.FS.realPath "tests/LF/stlc.elpi"
  let src := "import Elpi\nopen Elpi.Cmd\nelpi_program plain\nelpi_accumulate plain file \"" ++ path.toString ++ "\"\n" ++
    "#elpi plain lp%{ of (lam base x\\ lam base y\\ x) T }%\n"
  let msgs ← elabSource src
  check (errors msgs).isEmpty s!"errors: {errors msgs}"
  check ((infos msgs).any fun t => hasSub t "T = arr base (arr base base)") s!"{infos msgs}"

-- @tg: verifies:: [[openspec:elpi-lf#Totality checking#Total relation is reported as a meta-theorem]]
#eval show IO Unit from do
  let plus := "#lf\nnat : type.\nz : nat.\ns : nat -> nat.\nplus : nat -> nat -> nat -> type.\n#mode plus +N +M -P.\nplus_z : plus z M M.\nplus_s : plus (s N) M (s P) <- plus N M P.\n#total N (plus N _ _).\n"
  let src := header ++ "lf_signature arith lp%{\n" ++ plus ++ "}%\nlf_export arith\n#check @Arith.plus_total\n#print axioms Arith.plus_total\n"
  let msgs ← elabSource src
  check (errors msgs).isEmpty s!"errors: {errors msgs}"
  let all := " ".intercalate (infos msgs)
  check (hasSub all "plus is total in its first argument") s!"{all}"
  check (hasSub all "with inputs N and M and output P") s!"{all}"
  check (hasSub all "∀ (N M : Arith.Nat), ∃ P, Arith.Plus N M P") s!"{all}"
  check (hasSub all "does not depend on any axioms") s!"{all}"

-- @tg: verifies:: [[openspec:elpi-lf#Totality checking#Missing case is reported by coverage]]
#eval show IO Unit from do
  let plus := "#lf\nnat : type.\nz : nat.\ns : nat -> nat.\nplus : nat -> nat -> nat -> type.\n#mode plus +N +M -P.\nplus_s : plus (s N) M (s P) <- plus N M P.\n#total N (plus N _ _).\n"
  let src := header ++ "lf_signature arith lp%{\n" ++ plus ++ "}%\nlf_export arith\n#check @Arith.plus_total\n"
  let msgs ← elabSource src
  check ((errors msgs).any fun e => hasSub e "missing case `plus z M P`") s!"{errors msgs}"
  -- no meta-theorem was added
  check ((errors msgs).any fun e => hasSub e "plus_total") s!"plus_total must not exist: {errors msgs}"
  check (!(infos msgs).any fun t => hasSub t "is total") "no totality should be reported"

-- @tg: verifies:: [[openspec:elpi-lf#Defeq bridge#Bridge discharges a goal by Lean computation]]
#eval show IO Unit from do
  let br := "#lf\n#bridge nat = Nat.\n#bridge add : nat -> nat -> nat = Nat.add.\nsame : nat -> nat -> type.\nrefl : same N N.\n"
  let src := header ++ "lf_signature br lp%{\n" ++ br ++ "}%\n#lf_query br lp%{ same (add 2 3) 5 }%\nlf_export br\nlf_certify br five lp%{ same (add 2 3) 5 }%\n#print five\n#print axioms five\n"
  let msgs ← elabSource src
  check (errors msgs).isEmpty s!"errors: {errors msgs}"
  let all := " ".intercalate (infos msgs)
  check (hasSub all "proof: refl (add 2 3)") s!"{all}"
  check (hasSub all "theorem five : Br.Same (Nat.add 2 3) 5") s!"{all}"
  check (hasSub all "does not depend on any axioms") s!"{all}"
  -- a wrong computation is not an answer
  let src2 := header ++ "lf_signature br lp%{\n" ++ br ++ "}%\n#lf_query br lp%{ same (add 2 3) 6 }%\n"
  let msgs2 ← elabSource src2
  check ((errors msgs2).any fun e => hasSub e "no solution") s!"{errors msgs2}"
  -- without the bridge, `add` is rigid: the query is not answered
  let rigid := "#lf\nnat : type.\nadd : nat -> nat -> nat.\nsame : nat -> nat -> type.\nrefl : same N N.\n"
  let msgs3 ← elabSource (header ++ "lf_signature rg lp%{\n" ++ rigid ++ "}%\n#lf_query rg lp%{ same (add 2 3) 5 }%\n")
  check (!(infos msgs3).any fun t => hasSub t "proof:") s!"{msgs3}"

-- a wrong bridge result makes the certificate fail in the kernel
-- @tg: verifies:: [[openspec:elpi-lf#Defeq bridge#Bridge discharges a goal by Lean computation]]
#eval show IO Unit from do
  let br := "#lf\n#bridge nat = Nat.\n#bridge add : nat -> nat -> nat = Nat.add.\nsame : nat -> nat -> type.\nrefl : same N N.\n"
  let lying := "open Lean Elab Command Elpi.LF in\nrun_cmd do\n" ++
    "  let .ok sig := Elpi.LFCmd.getSig (← getEnv) \"br\" | throwError \"no sig\"\n" ++
    -- the engine's `add` multiplies: `same (add 2 3) 6` is found, but Lean computes `Nat.add 2 3 = 5`
    "  let fns : Std.HashMap String BridgeFn := ({} : Std.HashMap String BridgeFn).insert \"add\" ⟨2, fun a => a[0]! * a[1]!⟩\n" ++
    "  let .ok prog := elaborate sig fns | throwError \"elab\"\n" ++
    "  let [.ok a] := (runQuery sig prog \"same (add 2 3) 6\").take 1 | throwError \"the lying bridge found no answer\"\n" ++
    "  let .atom fam args := a.ty | throwError \"ty\"\n" ++
    "  try\n    liftCoreM (Elpi.LFCmd.certifyProof sig a.syms `six fam args a.proof (recheck := false))\n    logError \"ACCEPTED\"\n" ++
    "  catch e => logInfo m!\"REJECTED {e.toMessageData}\"\n#check six\n"
  let msgs ← elabSource (header ++ "lf_signature br lp%{\n" ++ br ++ "}%\nlf_export br\n" ++ lying)
  let all := " ".intercalate (infos msgs)
  check (hasSub all "REJECTED") s!"{msgs}"
  check ((errors msgs).any fun e => hasSub e "six") s!"six must not exist: {msgs}"
