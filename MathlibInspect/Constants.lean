import Mathlib.Tactic
import Auto.Tactic

open Lean Auto

def ConstantInfo.typeStr : ConstantInfo → String
| .axiomInfo _   => "axiomInfo"
| .defnInfo _    => "defnInfo"
| .thmInfo _     => "thmInfo"
| .opaqueInfo _  => "opaqueInfo"
| .quotInfo _    => "quotInfo"
| .inductInfo _  => "inductInfo"
| .ctorInfo _    => "ctorInfo"
| .recInfo _     => "recInfo"

def Expr.collectConstants (e : Expr) : HashSet Expr :=
  Expr.collectRawM (m := Id) Expr.isConst e

def Expr.collectNames (e : Expr) : HashSet Name :=
  HashSet.ofList ((Expr.collectConstants e).toList.map (fun e => e.constName))

namespace Inspect

def IO.randNats (min max attempt : Nat) : IO (HashSet Nat) := do
  return HashSet.ofList (← (List.range attempt).mapM (fun _ => IO.rand min max))

def Array.randChoice {α} (xs : Array α) (attempt : Nat) : IO (Array α) := do
  let randNats ← IO.randNats 0 (xs.size - 1) attempt
  let mut ret := #[]
  for i in randNats do
    if let .some x := xs[i]? then
      ret := ret.push x
  return ret

def allConstants (safe : Bool := false) (thm : Bool := false) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  let constants := env.constants.toList
  let filtered := constants.filter (fun (_, ci) =>
    (!safe || !ci.isUnsafe) && (!thm || ci.isThm))
  let mut ret := #[]
  for ci in filtered do
    ret := ret.push ci.snd
  return ret

def randConsts (attempt : Nat) (safe : Bool := true) (thm : Bool := false) : CoreM (Array ConstantInfo) := do
  let mut allcis ← allConstants safe thm
  return ← Array.randChoice allcis attempt

def constantType (name : Name) : CoreM String := do
  let .some ci := (← getEnv).find? name
    | throwError "constantType :: Unable to find {name}"
  return ConstantInfo.typeStr ci

def getAllDeclRangeEntries (env : Environment) : Array (Name × DeclarationRanges) :=
  let importedEntries := (declRangeExt.toEnvExtension.getState env).importedEntries
  let importedEntries := Array.concatMap id importedEntries
  let state := (declRangeExt.getState env).toList
  importedEntries.append (Array.mk state)

-- Weirdly, the `name` of a few (41) entries in the declaration range cannot
--   be found in the environment
def allConstsWithDeclRange : CoreM (Array ConstantInfo) := do
  let mut ret := #[]
  for (name, _) in getAllDeclRangeEntries (← getEnv) do
    if let .some ci := (← getEnv).find? name then
      ret := ret.push ci
  return ret

def allThmsWithDeclRange : CoreM (Array TheoremVal) := do
  return (← allConstsWithDeclRange).filterMap (fun ci =>
    match ci with
    | .thmInfo ti => .some ti
    | _ => .none)

def randConstsWithDeclRange (attempt : Nat) : CoreM (Array ConstantInfo) := do
  let all ← allConstsWithDeclRange
  return ← Array.randChoice all attempt

def randThmsWithDeclRange (attempt : Nat) : CoreM (Array TheoremVal) := do
  let all ← allThmsWithDeclRange
  return ← Array.randChoice all attempt

end Inspect

set_option trace.auto.mono.printLemmaInst true

open Inspect in
#eval do
  let names := (← randThmsWithDeclRange 20).map (fun (x : TheoremVal) => x.name)
  for name in names do
    IO.println name
    IO.println (repr name)
    IO.println (← constantType name)

open Inspect in
#eval do
  let w ← allThmsWithDeclRange
  IO.println w.size

open Inspect in
#eval do
  let w ← randThmsWithDeclRange 200
  let w := w.filter (fun (ti : TheoremVal) => ti.value.size > 512)
  IO.println w.size
  IO.println (w.map (fun (x : TheoremVal) => x.name))

#check 2

#print Ideal.eq_zero_of_polynomial_mem_map_range
