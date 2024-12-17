import Mathlib
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestCode

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
--set_option trace.auto.runAuto.printLemmas true
set_option trace.auto.eval.printResult true
--set_option trace.auto.tptp.printProof true

-- #eval @id (CoreM _) do
--   let all ← allHumanTheorems
--   let n := 128
--   NameArray.save (← Array.randPick all n) s!"MathlibNames{n}.txt"

-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .tptp (.zeport .lams) "/home/indprinciples/Programs/zipperposition/portfolio",
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- #eval namesFileEval
--   { solverConfig := .native,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .smt .cvc5,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

#check hasMFDerivWithinAt_extChartAt
#print CategoryTheory.ComposableArrows.ext₁
#print DFinsupp.lapply_comp_lsingle_of_ne
#print ENNReal.fun_eq_funMulInvSnorm_mul_eLpNorm
#print Set.toFinset_mul
