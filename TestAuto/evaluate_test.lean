import Mathlib
import Hammertest.DuperInterface
import Hammertest.DuperInterfaceRebindRaw
import Auto.EvaluateAuto.TestAuto
import Auto.EvaluateAuto.TestTactics
import Auto.EvaluateAuto.TestTranslation

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
--set_option trace.auto.runAuto.printLemmas true
set_option trace.auto.eval.printResult true
--set_option trace.auto.tptp.printProof true

-- #eval @id (CoreM _) do
--   let all ← allHumanTheoremsFromPackage "Mathlib"
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
--   { solverConfig := .smt .cvc5,
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

set_option auto.testTactics.ensureAesop true

-- #eval @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let m := Std.HashSet.ofList (← allHumanTheorems).toList
--   let r ← evalTacticsAtModule `Mathlib.Algebra.Group.Defs p (fun ci => m.contains ci.name)
--     { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 65536, .useAesopWithPremises 65536],
--       logFile := "evalTacticLog.txt", resultFile := "evalTacticResult.txt"
--       nonterminates := #[] }
--   trace[auto.tactic] "{r}"

-- set_option auto.testTactics.ensureAuto true
-- set_option auto.testTactics.rebindNativeModuleName "Hammertest.DuperInterfaceRebindRaw"
-- #eval @id (CoreM _) do
--   let p ← initSrcSearchPath
--   let m := Std.HashSet.ofList (← allHumanTheorems).toList
--   let r ← evalTacticsAtModule `Mathlib.Algebra.Group.Defs p (fun ci => m.contains ci.name)
--     { tactics := #[.testUnknownConstant, .useAesopWithPremises 65536, .useAuto true .native 10],
--       logFile := "evalTacticLog.txt", resultFile := "evalTacticResult.txt"
--       nonterminates := #[] }
--   trace[auto.tactic] "{r}"

-- #eval evalTacticsAtMathlibHumanTheorems
--   { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096], resultFolder := "./Eval",
--     nonterminates := #[], nprocs := 8 }

-- set_option auto.testTactics.ensureAuto true
-- set_option auto.testTactics.rebindNativeModuleName "Hammertest.DuperInterfaceRebindRaw"
-- #eval evalTacticsAtMathlibHumanTheorems
--   { tactics := #[.testUnknownConstant, .useAesopWithPremises 65536, .useAuto true .native 10], resultFolder := "./Eval",
--     nonterminates := #[], nprocs := 8 }

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

-- #eval do
--   let r ← readETMHTResult
--     { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096],
--       resultFolder := "/mnt/d/3_Tmp/EvalTactics", nonterminates := #[], nprocs := 4 }
--   let r := (r.map Prod.snd).flatMap id
--   let r := r.map Prod.snd
--   IO.println s!"Total : {r.size}"
--   for idx in [0:5] do
--     let t := r.map (fun r => match Prod.fst r[idx]! with | Result.success => 1 | _ => 0)
--     let t := t.foldl Nat.add 0
--     IO.println s!"{idx} : {t}"
--   let cumulative : Array Bool := r.map (fun s => Array.any s (
--      fun r => match Prod.fst r with | Result.success => true | _ => false))
--   let cumulative := cumulative.map (fun b : Bool => if b then 1 else 0)
--   let t := cumulative.foldl Nat.add 0
--   IO.println s!"cul : {t}"

-- #eval do
--   let r ← readEAMHTResult
--     { solverConfig := .native, batchSize := 512
--       resultFolder := "/mnt/d/3_Tmp/EvalAuto", nonterminates := #[], nprocs := 4 }
--   let r := r.map Prod.snd
--   IO.println s!"Total : {r.size}"
--   let cumulative : Array Bool := r.map (fun r =>
--     match r with | Result.success => true | _ => false)
--   let cumulative := cumulative.map (fun b : Bool => if b then 1 else 0)
--   let t := cumulative.foldl Nat.add 0
--   IO.println s!"cul : {t}"

-- #eval @id (CoreM _) do
--   let names ← NameArray.load "EvalResults/MathlibNames512.txt"
--   evalReduceSize names .default "EvalReduceDSize" 16 (8 * 1024 * 1024) 120

-- #eval @id (CoreM _) do
--   let names ← NameArray.load "EvalResults/MathlibNames128.txt"
--   evalAutoAtTheoremsAsync
--     { maxHeartbeats := 65535, timeout := 10,
--       solverConfig := .native, resultFolder := "EvalAutoDResult",
--       nprocs := 4, batchSize := 1,
--       memoryLimitKb := .some (8 * 1024 * 1024), timeLimitS := .some 60,
--       nonterminates := #[] }
--     names #[`Mathlib] #[
--       "set_option auto.mono.ignoreNonQuasiHigherOrder true",
--       "set_option auto.redMode \"default\""
--     ]

-- TODO: When elaborating identifier `Matroid.not_indep_iff` when proving
-- `Matroid.Base.insert_dep`, got `unknown level metavariable` error

-- Nonterminates when supplying auto with result of Term.exprToSyntax
-- (.useAuto true .native 10, \`\`IntermediateField.extendScalars_top),
-- (.useAuto true .native 10, \`\`continuous_of_const),
-- (.useAuto true .native 10, \`\`Polynomial.exists_separable_of_irreducible),
-- (.useAuto true .native 10, \`\`IntermediateField.extendScalars_inf),
-- (.useAuto true .native 10, \`\`IsLocallyConstant.of_constant)

-- #eval do
--   let w1 ← readETMHTEvaluateFiles
--       { tactics := #[.useRfl, .useAesopWithPremises 4096, .useAuto true .native 10],
--         resultFolder := "/mnt/d/3_Tmp/Eval_3/EvalAutoAsTactic", nonterminates := #[], nprocs := 4 }
--   let hs := Std.HashSet.ofArray (w1.snd.map Prod.fst)
--   let q := w1.fst.filter (fun n => !hs.contains n)
--   IO.println q

/-

import Mathlib
import Hammertest.DuperInterface
import Hammertest.DuperInterfaceRebindRaw
import Auto.EvaluateAuto.TestAuto
import Auto.EvaluateAuto.TestTactics
import Auto.EvaluateAuto.TestTranslation

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
set_option trace.auto.eval.printResult true

#eval @id (CoreM _) do
  let names ← NameArray.load "EvalResults/MathlibNames512.txt"
  evalReduceSize names .default "EvalReduceDSize" 16 (8 * 1024 * 1024) 120

-/

/-

import Mathlib
import Auto

open Lean Auto EvalAuto

#eval @id (CoreM _) do
  let names ← NameArray.load "EvalResults/MathlibNames512.txt"
  evalReduceSize names .default "EvalReduceDSize" 16 (8 * 1024 * 1024) 120

-/
