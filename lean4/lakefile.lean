import Lake
open Lake DSL

package "aggregators" where
  -- add package configuration options here

lean_lib «Aggregators» where
  -- add library configuration options here

@[default_target]
lean_exe "aggregators" where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
