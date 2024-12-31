import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/-- `merge_unique` preserves the base case `[]` -/
lemma merge_unique_base_case {α : Type} (r : α → α → Bool) :
  mergeUniqAgg r [] [] = [] :=
  by
    rw [mergeListAggNTR]

theorem sort_base_case {α : Type}
  (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : sort r [] = []) :
  (mergeListAggNTR r (sort r []) (sort r [])) = [] :=
  by
    rw [h, merge_base_case]
