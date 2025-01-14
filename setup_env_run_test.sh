#! Please run this script using `bash`
#! This script is only compatible with Lean v4.15.0
#! This script is only compatible with Mathlib4 29f9a66d622d9bab7f419120e22bb0d2598676ab, due to 'nonterminates'

wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout 8607f94a173a956486696df88822b37fc219bd1a; cd ..
git clone https://github.com/leanprover-community/duper
cd duper; git checkout 9cd4d4d1d71034d456d06aef2e4d07c911b88c65; cd ..
git clone https://github.com/PratherConid/lean-hammertest
cd lean-hammertest
source $HOME/.elan/env
lake build

echo "import Mathlib
import Auto.EvaluateAuto.TestAuto

open EvalAuto

#eval evalAutoAtMathlibHumanTheorems
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .native,
    resultFolder  := \"./EvalAuto\",
    nthreads := 32, batchSize := 512,
    nonterminates := #[
      \`\`Differentiable.exists_const_forall_eq_of_bounded,
      \`\`uniformContinuous_of_const,
      \`\`mem_pairSelfAdjointMatricesSubmodule',
      \`\`mem_selfAdjointMatricesSubmodule,
      \`\`Equiv.Perm.cycleFactorsFinset_eq_list_toFinset,
      \`\`Polynomial.IsSplittingField.of_algEquiv,
      \`\`AffineMap.lineMap_injective,
      \`\`Subalgebra.restrictScalars_top,
      \`\`NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra,
      \`\`StarSubalgebra.inf_toSubalgebra,
      \`\`NonUnitalStarAlgebra.top_toNonUnitalSubalgebra,
      \`\`StarSubalgebra.top_toSubalgebra
    ] }" | lake env lean --stdin

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics

open EvalAuto

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 16384, .useAesopWithPremises 16384],
    resultFolder := \"./EvalTactics\",
    nonterminates := #[], nthreads := 16 }" | lake env lean --stdin