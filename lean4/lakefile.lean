import Lake
open Lake DSL

package "Aggregators" where
  -- add package configuration options here

lean_lib «Synthesis» where
  -- add library configuration options here

lean_lib «Verification» where
  -- add library configuration options here

@[default_target]
lean_exe "aggregators" where
  root := `Main

lean_exe "sort" where
  root := `Aggregators.Sort

lean_exe "sortn" where
  root := `Aggregators.SortN

lean_exe "sortr" where
  root := `Aggregators.SortR

lean_exe "sortnr" where
  root := `Aggregators.SortNR

lean_exe "sortk1n" where
  root := `Aggregators.SortK1N

lean_exe "sortu" where
  root := `Aggregators.SortU

lean_exe "uniq" where
  root := `Aggregators.Uniq

lean_exe "uniqc" where
  root := `Aggregators.UniqC

lean_exe "concat" where
  root := `Aggregators.Concat

lean_exe "sum" where
  root := `Aggregators.Sum

lean_exe "headn1" where
  root := `Aggregators.HeadN1

lean_exe "tailn1" where
  root := `Aggregators.TailN1

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a51c88ccf9e815ba450c98271246c73b2296f3e7"
-- require aesop from git "https://github.com/leanprover-community/aesop"
