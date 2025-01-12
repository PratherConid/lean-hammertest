#! Please run this script using `bash`

wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout 12b16cc39d85cd430fa9da5ef23bc1c072e1c6ae; cd ..
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
      \`\`mem_selfAdjointMatricesSubmodule
    ] }" | lake env lean --stdin

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics

open EvalAuto

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 16384, .useAesopWithPremises 16384],
    resultFolder := "./EvalTactics",
    nonterminates := #[], nthreads := 32 }" | lake env lean --stdin