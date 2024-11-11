import Lake
open Lake DSL

package "aggregators" where
  -- add package configuration options here

lean_lib «Synthesis» where
  -- add library configuration options here

lean_lib «Verification» where
  -- add library configuration options here

@[default_target]
lean_exe "aggregators" where
  root := `Main

lean_exe "sortn" where
  root := `sortn

lean_exe "concat" where
  root := `concat

require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- require aesop from git "https://github.com/leanprover-community/aesop"
