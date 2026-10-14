import TestUtil
import Lean
open Elpi TestUtil

elpi_program cnt "main Args :- std.length Args N, print N."

-- @tg: verifies:: [[openspec:elpi-cli#Compiled program executables#Executable starts without parsing the program]]
#eval show IO Unit from do
  let before ← parserCalls.get
  let q ← runMain cnt.compiled ["a", "b", "c"]
  expectEq q 0 "exit status of the compiled program"
  expectEq (← parserCalls.get) before "program parser calls while running a compiled program"
