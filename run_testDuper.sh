cd lean-hammertest

echo "import Mathlib
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestAuto

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
set_option trace.auto.eval.printResult true

set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option maxHeartbeats 200000000
#eval runAutoOnNamesFile
  { solverConfig := .native, maxHeartbeats := 65536,
    logFile := \"evalAutoNativeSS.log\", resultFile := \"evalAutoNativeSS.result\",
    nonterminates := #[] }
  \"EvalResults/MathlibNames512.txt\"" | lake env lean --stdin

echo "import Mathlib
import Hammertest.DuperInterface
import Auto.EvaluateAuto.TestAuto

open Lean Meta Elab Auto EvalAuto

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option trace.auto.tactic true
set_option trace.auto.eval.printResult true

set_option maxHeartbeats 200000000
#eval runAutoOnNamesFile
  { solverConfig := .rawNative,
    logFile := \"evalAutoRawNativeSS.log\", resultFile := \"evalAutoRawNativeSS.result\",
    nonterminates := #[
      \`\`CategoryTheory.Functor.RightExtension.precomp_obj_hom_app,
      \`\`NormedSpace.dual_def,
      \`\`MeasureTheory.condexpL1CLM_lpMeas,
      \`\`AlgebraicGeometry.Scheme.app_eq,
      \`\`EuclideanGeometry.eq_orthogonalProjection_of_eq_subspace,
      \`\`Sym.instSubsingleton,
      \`\`LinearMap.IsSymm.tmul
    ] }
  \"EvalResults/MathlibNames512.txt\"" | lake env lean --stdin