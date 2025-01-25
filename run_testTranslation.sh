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

-- import Mathlib
-- import Auto

echo "open Lean Auto EvalAuto

#eval @id (CoreM _) do
  if !(← System.FilePath.isDir \"EvalMonoSize\") then
    IO.FS.createDir \"EvalMonoSize\"

set_option auto.mono.ignoreNonQuasiHigherOrder true

set_option maxHeartbeats 20000000
#eval @id (CoreM _) do
  let names ← NameArray.load \"EvalResults/MathlibNames512.txt\"
  evalMonoSize names \"EvalMonoSize/result.txt\" 65536" | lake env lean --stdin