import Mathlib
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestAuto
import Auto.EvaluateAuto.TestTactics

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
--     logFile := "evalAutoOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- set_option auto.mono.ignoreNonQuasiHigherOrder true
-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := "evalAutoOut.txt" }
--   "EvalResults/MathlibNames128.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .smt .z3,
--     logFile := "evalAutoOut.txt" }
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

set_option auto.evalAuto.ensureAesop true

-- open EvalAuto in
-- #eval @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let r ← runTacticsAtConstantDeclaration ``UInt32.toUInt16_toNat p
--     #[fun _ => useSimpAll, useSimpAllWithPremises, fun _ => useAesop, useAesopWithPremises]
--   trace[auto.tactic] "{r}"

-- open EvalAuto in
-- #eval @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let r ← evalAtModule `Mathlib.RingTheory.FiniteType p (fun ci => ci.name == ``AddMonoidAlgebra.mem_adjoin_support)
--     { tactics := #[.useRfl, .useSimp, .useAesop, .useAesopWithPremises], logFile := "evalTacticOut.txt" }
--   trace[auto.tactic] "{r}"

#check AddMonoidAlgebra.mem_adjoin_support

-- set_option maxHeartbeats 2000
-- theorem mem_adjoin_support.{u_1, u_2} {R : Type u_1} {M : Type u_2} [CommSemiring R] [AddMonoid M]
--   (f : AddMonoidAlgebra R M) : f ∈ Algebra.adjoin R (AddMonoidAlgebra.of' R M '' ↑f.support) := by
--   aesop
