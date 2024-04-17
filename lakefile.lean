import Lake
open Lake DSL

package hammertest {
  -- add package configuration options here
}

require auto from "../lean-auto/"

require Duper from "../duper/"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Hammertest {
  -- add library configuration options here
}

@[default_target]
lean_exe hammertest {
  root := `Main
}
