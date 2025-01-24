#!bash
# This script is only compatible with Lean v4.15.0
# This script is only compatible with Mathlib4 29f9a66d622d9bab7f419120e22bb0d2598676ab, due to 'nonterminates'
# The number of processes chosen by this script is compatible with Amazon EC2 c5ad.16xlarge

# Prerequisites
sudo apt-get update
yes | sudo apt-get install unzip

# Install z3
wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip
unzip -q z3-4.13.4-x64-glibc-2.35.zip -d .
rm z3-4.13.4-x64-glibc-2.35.zip
sudo cp ~/z3-4.13.4-x64-glibc-2.35/bin/z3 /usr/bin/z3

# Install cvc5
wget https://github.com/cvc5/cvc5/releases/download/latest/cvc5-Linux-x86_64-static-2025-01-17-6e83633.zip
unzip -q cvc5-Linux-x86_64-static-2025-01-17-6e83633.zip -d .
rm cvc5-Linux-x86_64-static-2025-01-17-6e83633.zip
sudo cp ~/cvc5-Linux-x86_64-static/bin/cvc5 /usr/bin/cvc5

# Install Lean and Lean libraries
wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout 5d1ff250315010b9380acf6f39202c6e2dbd1855; cd ..
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
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .smt .z3,
    resultFolder  := \"./EvalAutoZ3\",
    nprocs := 64, batchSize := 512,
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
import Auto.EvaluateAuto.TestAuto

open EvalAuto

#eval evalAutoAtMathlibHumanTheorems
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .smt .cvc5,
    resultFolder  := \"./EvalAutoCVC5\",
    nprocs := 64, batchSize := 512,
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