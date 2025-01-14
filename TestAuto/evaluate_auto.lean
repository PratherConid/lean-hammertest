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
      ``mem_selfAdjointMatricesSubmodule,
      ``Equiv.Perm.cycleFactorsFinset_eq_list_toFinset,
      ``Polynomial.IsSplittingField.of_algEquiv,
      ``AffineMap.lineMap_injective,
      ``Subalgebra.restrictScalars_top,
      ``NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra,
      ``StarSubalgebra.inf_toSubalgebra,
      ``NonUnitalStarAlgebra.top_toNonUnitalSubalgebra,
      ``StarSubalgebra.top_toSubalgebra
    ] }
