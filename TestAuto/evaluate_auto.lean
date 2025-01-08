import Mathlib
import Auto.EvaluateAuto.TestAuto

open EvalAuto

#eval evalAutoAtMathlibHumanTheorems
  { maxHeartbeats := 65536, timeout := 10, solverConfig := .native,
    resultFolder  := "./EvalAuto",
    nthreads := 4, batchSize := 512 }
