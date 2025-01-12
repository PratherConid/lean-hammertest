import Mathlib
import Auto.EvaluateAuto.TestAuto

open EvalAuto

#eval evalAutoAtMathlibHumanTheorems
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .native,
    resultFolder  := "./EvalAuto",
    nthreads := 4, batchSize := 512,
    nonterminates := #[
      ``Differentiable.exists_const_forall_eq_of_bounded,
      ``uniformContinuous_of_const,
      ``mem_pairSelfAdjointMatricesSubmodule',
      ``mem_selfAdjointMatricesSubmodule
    ] }
