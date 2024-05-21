import Hammertest.DuperInterface
import Duper.TPTP

-- Standard Preprocessing Configs
set_option auto.redMode "reducible"
-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zeport-fo"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw

set_option auto.native true
set_option trace.auto.lamReif.printResult true
set_option trace.auto.lamReif.printValuation true

set_option auto.tptp true
set_option trace.auto.tptp.premiseSelection true
