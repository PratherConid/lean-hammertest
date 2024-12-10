import Mathlib
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestCode

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
--set_option trace.auto.runAuto.printLemmas true
set_option trace.auto.eval.printResult true
--set_option trace.auto.tptp.printProof true


--set_option maxHeartbeats 200000000
--#eval randEval
--  { solverConfig := .tptp (.zeport .lams)  "/home/indprinciples/Programs/zipperposition/portfolio", logFile := "evalOut.txt" }
--  128

-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .tptp (.zeport .lams)  "/home/indprinciples/Programs/zipperposition/portfolio",
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

set_option maxHeartbeats 200000000
#eval namesFileEval
  { solverConfig := .native,
    logFile := "evalOut.txt" }
  "EvalResults/MathlibNames128.txt"
