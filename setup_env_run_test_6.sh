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
cd lean-auto; git checkout f1ed94c00377128e53fed4255985ebfa88fd5c48; cd ..
git clone https://github.com/leanprover-community/duper
cd duper; git checkout 9cd4d4d1d71034d456d06aef2e4d07c911b88c65; cd ..
git clone https://github.com/PratherConid/lean-hammertest
cd lean-hammertest
source $HOME/.elan/env
lake build

eval $(opam env)

echo "import Mathlib
import Auto.EvaluateAuto.TestTactics
import Hammertest.DuperInterfaceRebindRaw

open EvalAuto

set_option auto.testTactics.ensureAesop true
set_option auto.testTactics.ensureAuto true
set_option auto.testTactics.rebindNativeModuleName \"Hammertest.DuperInterfaceRebindRaw\"

#eval evalTacticsAtMathlibHumanTheorems
  { tactics := #[.testUnknownConstant, .useAuto true (.tptp .zipperposition \"zipperposition\") 10],
    resultFolder := \"./EvalAutoZipperpnAsTactic\",
    nonterminates := #[
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Differentiable.exists_const_forall_eq_of_bounded),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`uniformContinuous_of_const),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`mem_pairSelfAdjointMatricesSubmodule'),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`mem_selfAdjointMatricesSubmodule),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Equiv.Perm.cycleFactorsFinset_eq_list_toFinset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Polynomial.IsSplittingField.of_algEquiv),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`AffineMap.lineMap_injective),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Subalgebra.restrictScalars_top),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`NonUnitalStarAlgebra.inf_toNonUnitalSubalgebra),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`StarSubalgebra.inf_toSubalgebra),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`NonUnitalStarAlgebra.top_toNonUnitalSubalgebra),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`StarSubalgebra.top_toSubalgebra),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Base.insert_dep),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.basis_iff_basis'_subset_ground),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.basis_subset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.dep_of_ssubset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.subset_basis'_of_subset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.exists_base_subset_union_base),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.dual_base_iff'),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.dual_dual),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Base.compl_base_dual),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Base.compl_inter_basis_of_inter_basis),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.ground_not_base),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Coindep.exists_base_subset_compl),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.restrict_base),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.base_restrict),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.basis_restrict_of_subset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.basis_restriction),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.of_restriction),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Base.basis_of_restriction),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.transfer),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.exists_basis_subset_union_basis),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.exists_insert_of_not_basis),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.exchange),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.eq_exchange_of_diff_eq_singleton),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.augment),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Indep.closure_eq_setOf_basis_insert),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.subset_closure),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.indep_iff_forall_not_mem_closure_diff'),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Spanning.closure_eq_of_superset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Spanning.exists_base_subset),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Coindep.compl_spanning),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Coindep.closure_compl),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.ext_spanning),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.comapOn_dual_eq_of_bijOn),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.Basis.map),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.map_basis_iff),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.restrictSubtype_ground_base_iff),
      (.useAuto true (.tptp .zipperposition \"zipperposition\") 10, \`\`Matroid.restrictSubtype_ground_basis_iff)
    ], nprocs := 32 }" | lake env lean --stdin