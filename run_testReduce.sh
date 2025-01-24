cd lean-hammertest

echo "import Mathlib
import Auto

open Lean Auto EvalAuto

#eval @id (CoreM _) do
  let names ← NameArray.load \"EvalResults/MathlibNames512.txt\"
  evalReduceSize names .reducible \"EvalReduceRSize\" 16 (8 * 1024 * 1024) 120" | lake env lean --stdin

echo "import Mathlib
import Auto

open Lean Auto EvalAuto

#eval @id (CoreM _) do
  let names ← NameArray.load \"EvalResults/MathlibNames512.txt\"
  evalReduceSize names .default \"EvalReduceDSize\" 16 (8 * 1024 * 1024) 120" | lake env lean --stdin

echo "import Mathlib
import Auto

open Lean Auto EvalAuto

#eval @id (CoreM _) do
  let names ← NameArray.load \"EvalResults/MathlibNames512.txt\"
  evalReduceSize names .all \"EvalReduceASize\" 16 (8 * 1024 * 1024) 120" | lake env lean --stdin
