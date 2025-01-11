curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout 26d9cb3da795010b3e4e2110e155e8b13ed2c2c0; cd ..
git clone https://github.com/leanprover-community/duper
cd duper; git checkout a41cc06670aee9d4762a12a11574532c4077f52f; cd ..
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
    nthreads := 8, batchSize := 512 }" | lake env lean --stdin

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics

open EvalAuto

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.useRfl, .useSimpAll, .useSimpAllWithPremises, .useAesop 16384, .useAesopWithPremises 16384],
    resultFolder := "./EvalTactics",
    nonterminates := #[], nthreads := 8 }" | lake env lean --stdin