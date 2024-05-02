import Mathlib.Tactic
import Auto.Tactic

open Lean

def getClassOutParamMap : CoreM (SMap Name (Array Nat)) := do
  let env ← getEnv
  return (classExtension.getState env).outParamMap

def getClassNames : CoreM (Array Name) := do
  let outParamMap ← getClassOutParamMap
  return Array.mk <| outParamMap.toList.map (fun (name, _) => name)

def getInstanceNameMap : CoreM (PHashMap Name Meta.InstanceEntry) := do
  return (Meta.instanceExtension.getState (← getEnv)).instanceNames

def getInstanceEntry (name : Name) : CoreM Meta.InstanceEntry := do
  let instanceNameMap ← getInstanceNameMap
  if let .some entry := instanceNameMap.find? name then
    return entry
  else
    throwError "getInstanceEntry :: {name} is not an instance"

def getInstanceNames : CoreM (Array Name) := do
  let instanceNameMap ← getInstanceNameMap
  return instanceNameMap.toArray.map (fun (name, _) => name)

def getInstanceNamesContains (pattern : String) (caseSensitive : Bool := false) : CoreM (Array Name) := do
  let instanceNames ← getInstanceNames
  return instanceNames.filter (fun name =>
    let s := name.toString
    let s := if caseSensitive then s else s.toLower
    let pattern := if caseSensitive then pattern else pattern.toLower
    (s.findSubstr? pattern).isSome)

def getInstanceNamesBeginWith (nprefix : String) (caseSensitive : Bool := false) : CoreM (Array Name) := do
  let instanceNames ← getInstanceNames
  return instanceNames.filter (fun name =>
    let s := name.toString
    let s := if caseSensitive then s else s.toLower
    let ss := s.splitOn "."
    let nprefix := if caseSensitive then nprefix else nprefix.toLower
    let l := nprefix.length
    ss.any (fun s => s.take l == nprefix))
