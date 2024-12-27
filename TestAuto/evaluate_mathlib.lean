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

-- set_option auto.mono.ignoreNonQuasiHigherOrder true
-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- set_option maxHeartbeats 200000000
-- #eval namesFileEval
--   { solverConfig := .smt .z3,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

set_option trace.auto.mono true
set_option trace.auto.lamReif.printResult true

#check WeierstrassCurve.Affine.Point.map_id
#check RingHom.FiniteType.of_finite
#check List.map_concat
#check SuccOrder.nhdsWithin_Ici
#check isLUB_sSup
#check Set.image_preimage
#check WCovBy.le_of_lt
#check Encodable.axiom_of_choice

#eval runAutoOnConsts { solverConfig := .native }
  #[``AlgebraicGeometry.Spec.locallyRingedSpaceObj_sheaf']
#check AlgebraicGeometry.Spec.locallyRingedSpaceObj_sheaf'
