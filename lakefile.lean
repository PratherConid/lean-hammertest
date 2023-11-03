import Lake
open Lake DSL

package hammertest {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Duper from git
  "https://github.com/leanprover-community/duper.git"

require auto from git
  "https://github.com/avigad/lean-auto"

lean_lib Hammertest {
  -- add library configuration options here
}

@[default_target]
lean_exe hammertest {
  root := `Main
}
