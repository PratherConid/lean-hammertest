#!bash
# This script is only compatible with Lean v4.15.0
# This script is only compatible with Mathlib4 29f9a66d622d9bab7f419120e22bb0d2598676ab, due to 'nonterminates'
# The number of processes chosen by this script is compatible with Amazon EC2 c5ad.16xlarge

wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout 5a78deeaffe0582f312c637462543ec29eac5f5a; cd ..
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
set_option auto.testTactics.rebindNativeModuleName "Hammertest.DuperInterfaceRebindRaw"

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.testUnknownConstant, .useAesopWithPremises 16384, .useAuto .native 10],
    resultFolder := \"./EvalTactics\",
    nonterminates := #[
      (.useRfl, \`\`IntermediateField.extendScalars_top),
      (.useAesop 16384, \`\`IntermediateField.extendScalars_top),
      (.useAesopWithPremises 16384, \`\`IntermediateField.extendScalars_top),
      (.useRfl, \`\`IntermediateField.extendScalars_inf),
      (.useAesop 16384, \`\`IntermediateField.extendScalars_inf),
      (.useAesopWithPremises 16384, \`\`IntermediateField.extendScalars_inf),
      (.useRfl, \`\`Field.Emb.Cardinal.succEquiv_coherence),
      (.useAesop 16384, \`\`Field.Emb.Cardinal.succEquiv_coherence),
      (.useAesopWithPremises 16384, \`\`Field.Emb.Cardinal.succEquiv_coherence),
      (.useAesop 16384, \`\`UniformConvergenceCLM.uniformSpace_eq),
      (.useAesopWithPremises 16384, \`\`UniformConvergenceCLM.uniformSpace_eq)
    ], nprocs := 32 }" | lake env lean --stdin