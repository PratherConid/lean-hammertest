import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module

open Lean

def mathlibModules : CoreM (Array Name) := do
  let u := (← getEnv).header.moduleNames
  return u.filter (fun name => name.components[0]? == .some `Mathlib)

def getConstsOf (module : Name) : CoreM (Array Name) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throwError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, _) ← readModuleData mFile
  return mod.constNames

def theoremsIn (ns : Array Name) : CoreM (Array Name) := ns.filterM (fun n => do
  let ci? := (← getEnv).find? n
  let .some ci := ci?
    | return false
  return ci.isThm)
