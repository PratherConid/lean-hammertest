import Lean
import Auto.EvaluateAuto.TestAuto
import Auto.EvaluateAuto.TestTactics
import Auto.EvaluateAuto.TestTranslation

open Lean Meta EvalAuto

def tactics : CoreM (Array (Name × Array Result)) := do
  let r ← readETMHTResult
    { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 4096, .useAesopWithPremises 4096],
      resultFolder := "/mnt/d/3_Tmp/Eval_3/EvalTactics", nonterminates := #[], nprocs := 4 }
  let r := (r.map Prod.snd).flatMap id
  return r.map (fun (n, arr) => (n, arr.map Prod.fst))

def auto : CoreM (Array (Name × Result)) := do
  let r ← readEATAResult
    { solverConfig := .native, batchSize := 512
      resultFolder := "/mnt/d/3_Tmp/Eval_3/EvalAuto", nonterminates := #[], nprocs := 4 }
  return r.map (fun (n, r, _) => (n, r))

-- #eval @id (CoreM _) do
--   let aAll : Array (Name × Result) ← auto
--   let tcAll : Array (Name × Array Result) ← tactics
--   let tu : Array Name := (tcAll.filter (fun (_, rs) =>
--     match rs[0]? with | .some Result.success => true | _ => false)).map Prod.fst
--   let tcAll := tcAll.map (fun (n, rs) => (n, rs[1:].toArray))
--   let htu := Std.HashSet.ofArray tu
--   let aPre := aAll.filter (fun w => htu.contains (Prod.fst w))
--   let htu := Std.HashSet.ofArray (aPre.map Prod.fst)
--   let tc := tcAll.filter (fun w => htu.contains (Prod.fst w))
--   let htu := Std.HashSet.ofArray (tc.map Prod.fst)
--   let a := aPre.filter (fun w => htu.contains (Prod.fst w))
--   IO.println "EvalAutoResult"
--   IO.println aAll.size
--   IO.println a.size
--   IO.println (a.filter (fun w => Result.concise (Prod.snd w) == "S")).size
--   IO.println "EvalTacticsResult"
--   IO.println tcAll.size
--   let tc := tcAll.filter (fun w => htu.contains (Prod.fst w))
--   IO.println tc.size
--   for idx in [0:5] do
--     let t := tc.map (fun r => match (Prod.snd r)[idx]! with | Result.success => 1 | _ => 0)
--     let t := t.foldl Nat.add 0
--     IO.println s!"{idx} : {t}"
--   let cumulative : Array Name := (tc.filter (fun s => Array.any (Prod.snd s) (
--      fun r => match r with | Result.success => true | _ => false))).map Prod.fst
--   IO.println s!"cul : {cumulative.size}"
--   let culaesop : Array Name := (tc.filter (fun s =>
--     match (Prod.snd s)[3]?, (Prod.snd s)[4]? with
--     | .some Result.success, _ => true
--     | _, .some Result.success => true
--     | _, _ => false)).map Prod.fst
--   IO.println s!"culaesop : {culaesop.size}"
--   let hcumulative := Std.HashSet.ofArray cumulative
--   let auniq := a.filter (fun w => Result.concise (Prod.snd w) == "S" && !hcumulative.contains (Prod.fst w))
--   IO.println s!"auniq : {auniq.size}"
