import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestCode

open Lean Meta Elab Auto

#eval do
  let a ← analyze
  IO.println a

#eval mathlibModules
#eval do
  let a ← Name.getConstsOfModule `Mathlib.Data.Finset.Density
  a.filterM Name.isHumanTheorem

#eval do
  let a ← allHumanTheorems
  IO.println a.size

#check 2
#check initializing
#check Environment
#check Lean.PersistentEnvExtension.toEnvExtension

set_option trace.auto.tactic true
set_option trace.auto.runAuto.printLemmas true
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
set_option maxHeartbeats 50000

-- bug
#eval do
  let m ← runAutoOnConst ``Nat.sub_one_lt_of_lt
  trace[auto.tactic] m!"{m}"

#eval do
  let m ← runAutoOnConst ``Nat.sub_add_cancel
  trace[auto.tactic] m!"{m}"
