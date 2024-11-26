import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Hammertest.MathLibAnalyze.Constants

open HammerTest

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
