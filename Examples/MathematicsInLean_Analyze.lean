import Lean
import Std.Data.String

/-
  Analyze `MathematicsInLean.lean`
-/

open Lean

structure ThmResult where
  manualProof : String
  autoProof : String

def ThmResult.toString : ThmResult → String
| ⟨manual, auto⟩ => "{manualProof := " ++ manual ++ ", autoProof := " ++ auto ++ "}"

instance : ToString ThmResult where
  toString := ThmResult.toString

-- inl : Namespace, inr : Section
def GroupContext := Array (String ⊕ String)

def GroupContext.transition? (ctx : GroupContext) (s : String) : Option GroupContext :=
  let sNamespace := s.splitOn "namespace "
  let sSection := s.splitOn "section"
  if s == "end" || s.take 4 == "end " || (s.findSubstr? " end ").isSome then
    if ctx.size >= 1 then .some ctx.pop else .none
  else if h : sNamespace.length > 1 then
    let afterNamespace := sNamespace.get ⟨1, h⟩
    let name := (afterNamespace.dropWhile Char.isWhitespace).dropRightWhile Char.isWhitespace
    .some (ctx.push (.inl name))
  else if h : sSection.length > 1 then
    let afterSection := sSection.get ⟨1, h⟩
    let name := (afterSection.dropWhile Char.isWhitespace).dropRightWhile Char.isWhitespace
    .some (ctx.push (.inr name))
  else
    .some ctx

def GroupContext.prefix (ctx : GroupContext) : Array String := ctx.filterMap (fun x =>
  match x with
  | .inl name => .some name
  | .inr _ => .none)

def readMathematicsInLean : IO String :=
  IO.FS.withFile s!"./Examples/MathematicsInLean.lean" .read IO.FS.Handle.readToEnd

def parseMathematicsInLean (file : String) :
  HashMap String ThmResult × /- Result -/
  Array String /- Theorems that cannot be parsed -/ := Id.run <| do
  let mut inThm := false
  let mut curThm : Array String := #[]
  let mut grCtx : GroupContext := #[]
  let mut error : Array String := #[]
  let mut manualMap : HashMap String String := HashMap.empty
  let mut autoMap : HashMap String String := HashMap.empty
  for line in file.splitOn "\n" do
    let .some grCtxTr := grCtx.transition? line
      | error := error.push "Group Context Error"; grCtx := #[]
    grCtx := grCtxTr
    if inThm then
      if !line.all (fun x => x.isWhitespace) then
        curThm := curThm.push line
      else
        inThm := false
        let thmStr := String.intercalate "\n" curThm.data
        let firstLine := curThm.getD 0 ""
        let afterThm := (firstLine.splitOn "theorem ").getD 1 ""
        let thmName := (afterThm.splitOn " ").getD 0 ""
        if thmName != "" then
          if thmName.takeRight 5 == ".auto" then
            let thmName := thmName.dropRight 5
            let thmName := String.intercalate "." (grCtx.prefix.push thmName).data
            autoMap := autoMap.insert thmName thmStr
          else
            let thmName := String.intercalate "." (grCtx.prefix.push thmName).data
            manualMap := manualMap.insert thmName thmStr
        else
          error := error.push thmStr
    else
      if (line.findSubstr? "theorem").isSome then
        inThm := true
        curThm := #[line]
  let mut result : HashMap String ThmResult := HashMap.empty
  for (name, thmManual) in manualMap.toArray do
    let .some thmAuto := autoMap.find? name
      | error := error.push thmManual
    result := result.insert name { manualProof := thmManual, autoProof := thmAuto }
  return (result, error)

def analyze (results : HashMap String ThmResult) : IO Unit := do
  let results := results.toList.map Prod.snd
  let nTheorems := results.length
  IO.println s!"Total number of theorems: {nTheorems}"
  let success := results.filter (fun ⟨_, auto⟩ => !(auto.findSubstr? "autoFailSorry").isSome)
  IO.println s!"Total number of success: {success.length}"
  let proofBody (s : String) := String.intercalate ":=" ((s.splitOn ":=").drop 1)
  let manualTotal := success.foldl (fun sum ⟨manual, _⟩ => sum + (proofBody manual).length) 0
  let autoTotal := success.foldl (fun sum ⟨_, auto⟩ => sum + (proofBody auto).length) 0
  IO.println s!"Total length of manual proof: {manualTotal}"
  IO.println s!"Total length of auto proof: {autoTotal}"
  IO.println s!"Shortening: {Float.ofNat manualTotal / Float.ofNat autoTotal}"
  let ratios := success.map (fun ⟨manual, auto⟩ =>
    Float.ofNat (proofBody manual).length / Float.ofNat (proofBody auto).length)
  let ratioGreaterThanOne := ratios.filter (fun x => x > 1)
  IO.println s!"Total number of theorems whose proof is shortened: {ratioGreaterThanOne.length}"
  let meanRatioGreaterThanOne :=
   (List.foldl (· + ·) (Float.ofNat 0) ratioGreaterThanOne) / (Float.ofNat ratioGreaterThanOne.length)
  IO.println s!"Average Shortening per Theorem: {meanRatioGreaterThanOne}"

#eval do
  let file ← readMathematicsInLean
  let (parse, error) := parseMathematicsInLean file
  analyze parse
