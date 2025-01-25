import Lean
import Mathlib
import Auto.EvaluateAuto.TestAuto
import Auto.EvaluateAuto.TestTactics
import Auto.EvaluateAuto.TestTranslation

open Lean Meta EvalAuto

def readETMHTEvaluateFilesCached (path : String) : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  if !(← System.FilePath.pathExists (path ++ "/gatheredResult")) then
    gatherETMHTResult
      { tactics := Inhabited.default, resultFolder := path,
        nonterminates := Inhabited.default,
        nprocs := Inhabited.default }
  readEvalTacticsAtModuleResult (path ++ "/gatheredResult")

-- Shouldn't be used in the main evaluation section
def autoNative : CoreM (Array (Name × Result × Nat × Nat)) := readEATAResult
    { solverConfig := .native, batchSize := 512
      resultFolder := "/mnt/d/3_Tmp/Eval_1/EvalAuto", nonterminates := #[], nprocs := 4 }

def tactics : CoreM (Array (Name × Array (Result × Nat × Nat))) :=
  readETMHTEvaluateFilesCached "/mnt/d/3_Tmp/Eval_2/EvalTactics"

def autoNativeAsTactic : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  readETMHTEvaluateFilesCached "/mnt/d/3_Tmp/Eval_2/EvalAutoNativeAsTactic"

def autoZ3AsTactic : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  readETMHTEvaluateFilesCached "/mnt/d/3_Tmp/Eval_2/EvalAutoZ3AsTactic"

def autoCVC5AsTactic : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  readETMHTEvaluateFilesCached "/mnt/d/3_Tmp/Eval_2/EvalAutoCVC5AsTactic"

def autoZipperpnAsTactic : CoreM (Array (Name × Array (Result × Nat × Nat))) := do
  readETMHTEvaluateFilesCached "/mnt/d/3_Tmp/Eval_2/EvalAutoZipperpnAsTactic"

/--
  Order of tactics:
    testUnknownConstant, useRfl, useSimpAll,
    useSimpAllWithPremises, useAesop 65536, useAesopWithPremises 65536,
    useAuto true .native 10, useAuto true (.smt .z3) 10,
    useAuto true (.smt .cvc5) 10, useAuto true (.tptp .zipperposition "zipperposition") 10
-/
def allResults : CoreM (Array String × Array (Name × Array (Result × Nat × Nat))) := do
  let tt := Std.HashMap.ofList (← tactics).toList
  let an := Std.HashMap.ofList (← autoNativeAsTactic).toList
  let az := Std.HashMap.ofList (← autoZ3AsTactic).toList
  let ac := Std.HashMap.ofList (← autoCVC5AsTactic).toList
  let azp := Std.HashMap.ofList (← autoZipperpnAsTactic).toList
  let names := Array.foldl
    (fun a b => a.filter b.contains)
    (tt.toArray.map Prod.fst) #[an, az, ac, azp]
  let mut ret := #[]
  for name in names do
    let .some ntt := tt.get? name
      | throwError "{decl_name%} :: Unexpected result"
    let .some #[_, nan] := an.get? name
      | throwError "{decl_name%} :: Unexpected result"
    let .some #[_, naz] := az.get? name
      | throwError "{decl_name%} :: Unexpected result"
    let .some #[_, nac] := ac.get? name
      | throwError "{decl_name%} :: Unexpected result"
    let .some #[_, nazp] := azp.get? name
      | throwError "{decl_name%} :: Unexpected result"
    ret := ret.push (name, ntt ++ #[nan, naz, nac, nazp])
  let tactics := #[
    "testUnknownConstant", "rfl", "simpAll",
    "simpAllWithPremises", "aesop", "aesopWithPremises",
    "autoNative", "autoZ3", "autoCVC5", "autoZipperpn"
  ]
  return (tactics, ret)

def saveAllResults (path : String) : CoreM Unit := do
  let fhandle ← IO.FS.Handle.mk path .write
  let (tactics, results) ← allResults
  fhandle.putStrLn (String.intercalate " " tactics.toList)
  for ((name, result), idx) in results.zipWithIndex do
    let resultStrs := result.map (fun (r, time, hb) => s!"{r.concise} {time} {hb}")
    fhandle.putStrLn s!"{idx} {resultStrs} {Name.uniqRepr name}"

-- #eval saveAllResults "/mnt/d/3_Tmp/Eval_2/allResults"

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

def sumNatArr (arr : Array Nat) : Nat := Array.foldl Nat.add 0 arr

def sumFloatArr (arr : Array Float) : Float := Array.foldl Float.add 0 arr

def avgNatArr (arr : Array Nat) : Float := Float.ofNat (sumNatArr arr) / (Float.ofNat arr.size)

def avgFloatArr (arr : Array Float) : Float := sumFloatArr arr / (Float.ofNat arr.size)

def analyzeEvalReduceResult (path : String) : CoreM Unit := do
  let result ← readEvalReduceSizeResult path
  let fails := result.filterMap (fun (_, r) =>
    match r with
    | Except.error e => .some e
    | _ => .none)
  let failsTally := Auto.tallyArrayHashable fails
  IO.println s!"#Fails: {fails.size}"
  IO.println failsTally
  let sizeCmp := result.filterMap (fun (name, e) =>
    match e with
    | Except.ok n => .some (name, n)
    | _ => .none)
  let sizeCmp ← sizeCmp.mapM (fun (name, n) => do
    let .some ci := (← getEnv).find? name
      | throwError "Unexpected error"
    return (Expr.sizeWithoutSharing ci.type, n))
  let avgBefore := avgNatArr (sizeCmp.map Prod.fst)
  let avgAfter := avgNatArr (sizeCmp.map Prod.snd)
  let incTimes := sizeCmp.map (fun (before, after) => Float.ofNat after / Float.ofNat before)
  let numInc10 := incTimes.filter (fun x => x > 10.0)
  let avgInc := avgFloatArr incTimes
  IO.println s!"Successes : {sizeCmp.size}"
  IO.println s!"Avg size before : {avgBefore}, after : {avgAfter}"
  IO.println s!"Avg inc : {avgInc}, inc10 : {numInc10.size}"

-- #eval analyzeEvalReduceResult "/mnt/d/3_Tmp/Eval_2/EvalReduceRSize"
-- #eval analyzeEvalReduceResult "/mnt/d/3_Tmp/Eval_2/EvalReduceDSize"
-- #eval analyzeEvalReduceResult "/mnt/d/3_Tmp/Eval_2/EvalReduceASize"

def analyzeEvalMonoSizeResultHelper (result : Array (Name × Nat × Option Nat)) : CoreM Unit := do
  let success := result.filterMap (fun (name, raw, mon?) =>
    match mon? with
    | .some mon => .some (name, raw, mon)
    | .none => .none)
  IO.println s!"#Fails: {result.size - success.size}"
  IO.println s!"Successes : {success.size}"
  let avgBefore := avgNatArr (success.map (fun r => r.snd.fst))
  let avgAfter := avgNatArr (success.map (fun r => r.snd.snd))
  let incTimes := success.map (fun (_, before, after) => Float.ofNat after / Float.ofNat before)
  let avgInc := avgFloatArr incTimes
  IO.println s!"Avg size before : {avgBefore}, after : {avgAfter}"
  IO.println s!"Avg inc : {avgInc}"

def analyzeEvalMonoSizeResult (path : String) := do
  let result ← readEvalMonoSizeResult path
  analyzeEvalMonoSizeResultHelper result

-- #eval analyzeEvalMonoSizeResult "../lean-hammertest/EvalMonoSize/result.txt"
-- #eval @id (CoreM _) do
--   let an ← autoNative
--   let successes : Array Name := an.filterMap (fun (n, r, _) =>
--     if r.concise == "S" then .some n else .none)
--   let successes : Std.HashSet Name := Std.HashSet.ofArray successes
--   let result ← readEvalMonoSizeResult "../lean-hammertest/EvalMonoSize/result.txt"
--   let resultFiltered := result.filter (fun (n, _) => successes.contains n)
--   analyzeEvalMonoSizeResultHelper resultFiltered

-- #eval @id (CoreM _) do
--   let an ← autoNativeAsTactic
--   let successes : Array Name := an.filterMap (fun (n, r) =>
--     if (Prod.fst (r.get! 1)).concise == "S" then .some n else .none)
--   let hs : Std.HashSet Name := Std.HashSet.ofArray successes
--   let bn ← autoZ3AsTactic
--   let successes : Array Name := bn.filterMap (fun (n, r) =>
--     if (Prod.fst (r.get! 1)).concise == "S" then .some n else .none)
--   let hs := hs.insertMany successes
--   let cn ← autoCVC5AsTactic
--   let successes : Array Name := cn.filterMap (fun (n, r) =>
--     if (Prod.fst (r.get! 1)).concise == "S" then .some n else .none)
--   let hs := hs.insertMany successes
--   IO.println hs.size
