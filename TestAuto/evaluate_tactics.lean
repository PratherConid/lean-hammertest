import Mathlib
import Auto.EvaluateAuto.TestTactics

open EvalAuto

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096],
    resultFolder := "./EvalTactics",
    nonterminates := #[], nthreads := 4 }

-- #eval do
--   let r ← readTacticEvalResult
--     { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096], resultFolder := "./Eval",
--       nonterminates := #[], nthreads := 4 }
--   let r := (r.map Prod.snd).flatMap id
--   let r := r.map Prod.snd
--   IO.println s!"Total : {r.size}"
--   for idx in [0:5] do
--     let t := r.map (fun r => match r[idx]! with | Result.success => 1 | _ => 0)
--     let t := t.foldl Nat.add 0
--     IO.println s!"{idx} : {t}"
--   let cumulative : Array Bool := r.map (fun s => Array.any s (
--      fun r => match r with | Result.success => true | _ => false))
--   let cumulative := cumulative.map (fun b : Bool => if b then 1 else 0)
--   let t := cumulative.foldl Nat.add 0
--   IO.println s!"cul : {t}"
