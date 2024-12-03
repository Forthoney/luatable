import Lake
open Lake DSL

package "luatable" where
  version := v!"0.1.0"

lean_lib «Luatable» where
  -- add library configuration options here

@[default_target]
lean_exe "luatable" where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
