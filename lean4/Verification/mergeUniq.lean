import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/-- `mergeUniqAgg` preserves the base case `[]` -/
lemma merge_unique_base_case : mergeUniqAgg [] [] = [] :=
  by
    rw [mergeUniqAgg]

namespace MergeUniqExample

opaque foo : List String → List String
axiom foo_base_case : foo [] = []

theorem parallel_foo_base_case :
  (mergeUniqAgg (foo []) (foo [])) = [] :=
  by
    rw [foo_base_case]
    rw [merge_unique_base_case]

end MergeUniqExample
