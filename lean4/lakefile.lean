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

lean_exe "sort" where
  root := `Aggregators.sort

lean_exe "sortn" where
  root := `Aggregators.sortn

lean_exe "sortr" where
  root := `Aggregators.sortr

lean_exe "sortnr" where
  root := `Aggregators.sortnr

lean_exe "uniq" where
  root := `Aggregators.uniq

lean_exe "uniqc" where
  root := `Aggregators.uniqc

lean_exe "concat" where
  root := `Aggregators.concat

lean_exe "sum" where
  root := `Aggregators.sum

lean_exe "headn1" where
  root := `Aggregators.headn1

lean_exe "tailn1" where
  root := `Aggregators.tailn1

require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- require aesop from git "https://github.com/leanprover-community/aesop"
