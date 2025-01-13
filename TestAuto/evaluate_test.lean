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
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[] }
--   "EvalResults/MathlibNames128.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .tptp .zipperposition "/home/indprinciples/.opam/zipper/bin/zipperposition",
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[] }
--   "EvalResults/MathlibNames128.txt"

-- set_option auto.mono.ignoreNonQuasiHigherOrder true
-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[] }
--   "EvalResults/MathlibNames512.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .smt .z3,
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[] }
--   "EvalResults/MathlibNames128.txt"

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .rawNative,
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[] }
--   "EvalResults/MathlibNames128.txt"

set_option trace.auto.mono true
set_option trace.auto.lamReif.printResult true

-- Incompleteness
#check WeierstrassCurve.Affine.Point.map_id
#check List.map_concat
#check isLUB_sSup
#check Set.image_preimage
#check WCovBy.le_of_lt

-- Monomorphization
#check BoxIntegral.Box.dist_le_distortion_mul

set_option auto.evalAuto.ensureAesop true

-- #check @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let r ← runTacticsAtConstantDeclaration ``UInt32.toUInt16_toNat p
--     #[fun _ => useSimpAll, useSimpAllWithPremises, fun _ => useAesop 16384, useAesopWithPremises 16384]
--   trace[auto.tactic] "{r}"

-- #eval @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let m := Std.HashSet.ofList (← allHumanTheorems).toList
--   let r ← evalAtModule `Mathlib.Algebra.Group.Defs p (fun ci => m.contains ci.name)
--     { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 16384, .useAesopWithPremises 16384],
--       logFile := "evalTacticLog.txt", resultFile := "evalTacticResult.txt"
--       nonterminates := #[] }
--   trace[auto.tactic] "{r}"

-- #eval evalTacticsAtMathlibHumanTheorems
--   { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096], resultFolder := "./Eval",
--     nonterminates := #[], nthreads := 8 }

-- set_option trace.auto.runAuto.printLemmas true
-- #eval runAutoOnConsts
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := .none, resultFile := .none,
--     nonterminates := #[] }
--   #[``StarSubalgebra.top_toSubalgebra]

-- set_option maxHeartbeats 200000000
-- #eval runAutoOnNamesFile
--   { solverConfig := .native, maxHeartbeats := 65536,
--     logFile := "evalAutoLog.txt", resultFile := "evalAutoResult.txt",
--     nonterminates := #[``Subalgebra.restrictScalars_top] }
--   "EvalAuto/83.names"
