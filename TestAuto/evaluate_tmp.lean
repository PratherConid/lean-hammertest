import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestCode

open Lean Meta Elab Auto EvalAuto

#eval do
  let a ← analyze
  IO.println a

#eval mathlibModules
#eval do
  let a ← Name.getConstsOfModule `Mathlib.Data.Finset.Density
  a.filterM Name.isHumanTheorem

#eval do
  let a ← allHumanTheorems
  IO.println a.size

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
--set_option trace.auto.runAuto.printLemmas true
set_option trace.auto.eval.printResult true
--set_option trace.auto.tptp.printProof true

--set_option maxHeartbeats 200000000
--#eval randEval
--  { solverConfig := .native, logFile := "evalOut.txt" }
--  64
