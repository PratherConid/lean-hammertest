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
--   let n := 512
--   NameArray.save (← Array.randPick all n) s!"MathlibNames{n}.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .tptp (.zeport .lams) "/home/indprinciples/Programs/zipperposition/portfolio",
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- set_option auto.mono.ignoreNonQuasiHigherOrder true
-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames512.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .smt .z3,
--     logFile := "evalOut.txt" }
--   "EvalResults/MathlibNames128.txt"

set_option trace.auto.mono true
set_option trace.auto.lamReif.printResult true

-- Incompleteness
#check WeierstrassCurve.Affine.Point.map_id
#check RingHom.FiniteType.of_finite
#check List.map_concat
#check SuccOrder.nhdsWithin_Ici
#check isLUB_sSup
#check Set.image_preimage
#check WCovBy.le_of_lt


-- **TODO:** `aesop` behavior on `Set.image_preimage` is different!!
open EvalAuto in
#eval @id (CoreM _) do
  let p ← initSrcSearchPath
  let r ← runTacticsAtConstantDeclaration ``UInt32.toUInt16_toNat p
    #[fun _ => useSimpAll, useSimpAllWithPremises, fun _ => useAesop]
  trace[auto.tactic] "{r}"
