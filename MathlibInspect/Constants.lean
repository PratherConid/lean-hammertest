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

def allConstNames : CoreM (List Name) := do
  let env ← getEnv
  return env.constants.toList.map Prod.fst

def randConstNames (attempt : Nat) (safe : Bool := true) : CoreM (Array Name) := do
  let mut allNames ← allConstNames
  if safe then
    allNames ← allNames.filterM (fun name => do
      let .some ci := (← getEnv).find? name
        | throwError "randConstNames :: Unable to find {name}"
      return !ci.isUnsafe)
  let indexSet := HashSet.ofList (← (List.range attempt).mapM
    (fun _ => IO.rand 0 allNames.length))
  let mut names := #[]
  let mut cnt := 0
  for name in allNames do
    if indexSet.contains cnt then
      names := names.push name
    cnt := cnt + 1
  return names

def constantType (name : Name) : CoreM String := do
  let .some ci := (← getEnv).find? name
    | throwError "constantType :: Unable to find {name}"
  return ConstantInfo.typeStr ci

#eval do
  let names ← randConstNames 20
  for name in names do
    IO.println name
    IO.println (repr name)
    IO.println (← constantType name)

#check 2
#check ``Nat
#print LinearMap.isScalarTower_of_injective

end Inspect

set_option trace.auto.mono.printLemmaInst true

theorem TopologicalSpace.empty_nmem_countableBasis_me.{u} : ∀ (α : Type u) [t : TopologicalSpace α]
  [inst : SecondCountableTopology α], ∅ ∉ TopologicalSpace.countableBasis α := by
  let lem₁ := TopologicalSpace.exists_countable_basis.{u}
  auto [Classical.choose_spec] d[TopologicalSpace.countableBasis]

def testMonomorphizationOn (name : Name) : CoreM
