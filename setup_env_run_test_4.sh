#!bash
# This script is only compatible with Lean v4.15.0
# This script is only compatible with Mathlib4 29f9a66d622d9bab7f419120e22bb0d2598676ab, due to 'nonterminates'
# The number of processes chosen by this script is compatible with Amazon EC2 c5ad.16xlarge
# This scripts might break when `opam` releases new versions

# Prerequisites
sudo apt-get update
yes | sudo apt-get install unzip build-essential make cmake bubblewrap libgmp3-dev expect pkg-config

# Install zipperposition
printf "\n" | sudo bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
echo "set timeout -1
spawn opam init
expect {
    \"Sandboxing is not working\"      {send "y"; exp_continue}
    \"Do you want opam to configure\"  {send "5"}
}
expect eof
" | expect
opam switch create zipperpn 4.14.0
opam switch zipperpn
eval $(opam env)
echo "set timeout -1
spawn opam install zipperposition
expect \"Proceed with\"
send "y"
expect eof
" | expect
echo "set timeout -1
spawn opam pin -k git https://github.com/sneeuwballen/zipperposition.git#050072e01d8539f9126993482b595e09f921f66a
expect \"This will pin the following packages\"
send "y"
expect \"Proceed with\"
send "y"
expect eof
" | expect

# Install Lean and Lean libraries
wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
git clone https://github.com/leanprover-community/lean-auto
# TODO: Use up-to-date version
cd lean-auto; git checkout f94d6c6d256bd666c07162e8f2a5115e83ea2692; cd ..
git clone https://github.com/leanprover-community/duper
cd duper; git checkout 9cd4d4d1d71034d456d06aef2e4d07c911b88c65; cd ..
git clone https://github.com/PratherConid/lean-hammertest
cd lean-hammertest
source $HOME/.elan/env
lake build

eval $(opam env)

echo "import Mathlib
import Auto.EvaluateAuto.TestAuto

open EvalAuto

#eval evalAutoAtMathlibHumanTheorems
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .tptp .zipperposition \"zipperposition\",
    resultFolder  := \"./EvalAutoZipperpn\",
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