import Mathlib.Tactic.Ring
import Hammertest.DuperInterface

-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio/portfolio.lams.parallel.py"
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.duperRaw"

set_option auto.native true
set_option auto.tptp true

example (x y z : Int) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  ring

example (x y z : Int) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  simp [two_mul, pow_two]
  auto [add_mul, mul_add, add_comm, mul_comm, add_assoc]

variable {R : Type _} [CommRing R]

example (x y z : R) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  ring

example (x y z : R) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by
  simp [two_mul, pow_two]
  auto [add_mul, mul_add, add_comm, mul_comm, add_assoc]
