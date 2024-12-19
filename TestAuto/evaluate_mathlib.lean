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

-- **TODO:** tyDefEq.mode
-- **TODO:** tyDefEq.mode
-- #eval namesFileEval
--   { solverConfig := .native,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames512.txt"

-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .smt .cvc5,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"


#print finCongr_symm_apply

set_option trace.auto.mono true
set_option trace.auto.lamReif.printResult true

#check alexDiscEquivPreord_functor
#check WeierstrassCurve.Affine.Point.map_id
#check Stream'.WSeq.append_assoc
#check SchwartzMap.derivCLM_apply
#check RingHom.FiniteType.of_finite
