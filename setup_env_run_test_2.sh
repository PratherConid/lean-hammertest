#!bash
# This script is only compatible with Lean v4.15.0
# This script is only compatible with Mathlib4 29f9a66d622d9bab7f419120e22bb0d2598676ab, due to 'nonterminates'
# The number of processes chosen by this script is compatible with Amazon EC2 c5ad.16xlarge

wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout b8e7e01bfc7c6a14606f3a3a52808c59bb21426c; cd ..
git clone https://github.com/leanprover-community/duper
cd duper; git checkout 9cd4d4d1d71034d456d06aef2e4d07c911b88c65; cd ..
git clone https://github.com/PratherConid/lean-hammertest
cd lean-hammertest
source $HOME/.elan/env
lake build

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics
import Hammertest.DuperInterfaceRebindRaw

open EvalAuto

set_option auto.testTactics.ensureAesop true
set_option auto.testTactics.ensureAuto true
set_option auto.testTactics.rebindNativeModuleName \"Hammertest.DuperInterfaceRebindRaw\"

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.testUnknownConstant, .useAuto true .native 10],
    resultFolder := \"./EvalAutoAsTactic\",
    nonterminates := #[
      (.useAuto true .native 10, \`\`Differentiable.exists_const_forall_eq_of_bounded),
      (.useAuto true .native 10, \`\`uniformContinuous_of_const),
      (.useAuto true .native 10, \`\`mem_pairSelfAdjointMatricesSubmodule'),
      (.useAuto true .native 10, \`\`mem_selfAdjointMatricesSubmodule),
      (.useAuto true .native 10, \`\`Equiv.Perm.cycleFactorsFinset_eq_list_toFinset),
      (.useAuto true .native 10, \`\`Polynomial.IsSplittingField.of_algEquiv),
      (.useAuto true .native 10, \`\`AffineMap.lineMap_injective),
      (.useAuto true .native 10, \`\`Subalgebra.restrictScalars_top),
      (.useAuto true .native 10, \`\`NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra),
      (.useAuto true .native 10, \`\`StarSubalgebra.inf_toSubalgebra),
      (.useAuto true .native 10, \`\`NonUnitalStarAlgebra.top_toNonUnitalSubalgebra),
      (.useAuto true .native 10, \`\`StarSubalgebra.top_toSubalgebra),
      (.useAuto true .native 10, \`\`IntermediateField.extendScalars_top),
      (.useAuto true .native 10, \`\`continuous_of_const),
      (.useAuto true .native 10, \`\`Polynomial.exists_separable_of_irreducible),
      (.useAuto true .native 10, \`\`IntermediateField.extendScalars_inf),
      (.useAuto true .native 10, \`\`IsLocallyConstant.of_constant)
    ], nprocs := 32 }" | lake env lean --stdin

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics
import Hammertest.DuperInterfaceRebindRaw

open EvalAuto

set_option auto.testTactics.ensureAesop true

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useAesop 65536],
    resultFolder := \"./EvalAesop\",
    nonterminates := #[
      (.useAesop 65536, \`\`IntermediateField.extendScalars_top),
      (.useAesop 65536, \`\`IntermediateField.extendScalars_inf),
      (.useAesop 65536, \`\`Field.Emb.Cardinal.succEquiv_coherence),
      (.useAesop 65536, \`\`UniformConvergenceCLM.uniformSpace_eq)
    ], nprocs := 32 }" | lake env lean --stdin

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics
import Hammertest.DuperInterfaceRebindRaw

open EvalAuto

set_option auto.testTactics.ensureAesop true

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useAesopWithPremises 65536],
    resultFolder := \"./EvalAesopWithPremises\",
    nonterminates := #[
      (.useAesopWithPremises 65536, \`\`IntermediateField.extendScalars_top),
      (.useAesopWithPremises 65536, \`\`IntermediateField.extendScalars_inf),
      (.useAesopWithPremises 65536, \`\`Field.Emb.Cardinal.succEquiv_coherence),
      (.useAesopWithPremises 65536, \`\`UniformConvergenceCLM.uniformSpace_eq)
    ], nprocs := 32 }" | lake env lean --stdin