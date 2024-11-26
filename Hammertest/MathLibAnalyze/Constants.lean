import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module

open Lean

namespace HammerTest

def Name.getConstsOfModule (module : Name) : CoreM (Array Name) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throwError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, _) ← readModuleData mFile
  return mod.constNames

/-- Used as a wrapper in other functions -/
def Name.getCi (name : Name) (parentFunc : String) : CoreM ConstantInfo := do
  let .some ci := (← getEnv).find? name
    | throwError "{parentFunc} :: Cannot find name {name}"
  return ci

/-- Used as a wrapper in other functions -/
def Name.hasValue (name : Name) (parentFunc : String) : CoreM Bool := do
  return (← Name.getCi name parentFunc).value?.isSome

/-- Used as a wrapper in other functions -/
def Name.getValue (name : Name) (parentFunc : String) : CoreM Expr := do
  let .some v := (← Name.getCi name parentFunc).value?
    | throwError "{parentFunc} :: {name} has no value"
  return v

def Name.isTheorem (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  let .thmInfo _ := ci
    | return false
  return true

def Name.isHumanTheorem (name : Name) : CoreM Bool :=
  return (← Lean.findDeclarationRanges? name).isSome && (← Name.isTheorem name)

def allHumanTheorems : CoreM (Array Name) := do
  let allConsts := (← getEnv).constants.toList.map Prod.fst
  let allHumanTheorems ← allConsts.filterM Name.isHumanTheorem
  return Array.mk allHumanTheorems

/-- Return the theorems that occurs in an expression -/
def Expr.getUsedTheorems (e : Expr) : CoreM (Array Name) :=
  e.getUsedConstants.filterM Name.isTheorem

/-- Return the theorems that are used in the declaration body of a constant -/
def Name.getUsedTheorems (name : Name) : CoreM (Array Name) := do
  let v ← Name.getValue name "Name.getUsedTheorems"
  Expr.getUsedTheorems v

/-- Return true if the expression `e` only uses constants present in `names` -/
def Expr.onlyUsesConsts (e : Expr) (names : Array Name) : Bool :=
  e.getUsedConstants.all (fun name => names.contains name)

/-- Return true if the declaration body of `name` only
  uses constants present in `names` -/
def Name.onlyUsesConsts (name : Name) (names : Array Name) : CoreM Bool := do
  let v ← Name.getValue name "Name.onlyUsesConsts"
  return Expr.onlyUsesConsts v names

/-- Return true if the type `name` only uses constants present in `names` -/
def Name.onlyUsesConstsInType (name : Name) (names : Array Name) : CoreM Bool := do
  let ci ← Name.getCi name "Name.onlyUsesConsts"
  return Expr.onlyUsesConsts ci.type names

def logicConsts : Array Name := #[
    ``True, ``False,
    ``Not, ``And, ``Or, ``Iff,
    ``Eq
  ]

def boolConsts : Array Name := #[
    ``Bool,
    ``true, ``false,
    ``Bool.and, ``Bool.or, ``Bool.xor, ``Bool.not,
    ``BEq, ``BEq.beq, ``bne, ``instBEqOfDecidableEq, ``instDecidableEqBool,
    ``ite, ``cond,
    ``Decidable, ``Decidable.decide
  ]

def Name.onlyLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name logicConsts

def Name.onlyBoolLogicInType (name : Name) :=
  Name.onlyUsesConstsInType name (logicConsts ++ boolConsts)

def analyze : CoreM Unit := do
  let a ← allHumanTheorems
  IO.println (← a.filterM Name.onlyLogicInType)
  IO.println (← a.filterM (fun name =>
    return (!(← Name.onlyLogicInType name)) && (← Name.onlyBoolLogicInType name)))

#eval analyze

def mathlibModules : CoreM (Array Name) := do
  let u := (← getEnv).header.moduleNames
  return u.filter (fun name => name.components[0]? == .some `Mathlib)

#eval mathlibModules
#eval do
  let a ← Name.getConstsOfModule `Mathlib.Data.Finset.Density
  a.filterM Name.isHumanTheorem

end HammerTest
