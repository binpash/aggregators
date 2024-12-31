import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

namespace SortTR

theorem merge_base_case {α : Type} (r : α → α → Bool) : mergeListAgg r [] [] = [] :=
  by
    rw [mergeListAgg]
    rw [mergeAuxList]
    apply List.reverse_nil

theorem sort_base_case {α : Type}
  (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : sort r [] = []) :
  (mergeListAgg r (sort r []) (sort r [])) = [] :=
  by
    rw [h, merge_base_case]

lemma merge_equal_length : ∀ l₁ l₂, (mergeListAgg r l₁ l₂).length = (l₁ ++ l₂).length :=
  by
    intro l₁ l₂
    induction l₁ generalizing l₂ with
    | nil =>
      rw [mergeListAgg]
      rw [mergeAuxList]
      simp only [List.reverse_nil, List.nil_append]
    | cons x l₁ ih =>
      induction l₂ with
        | nil =>
          rw [mergeListAgg]
          rw [mergeAuxList]
          simp [List.length_cons]
          simp [List.append_nil]
        | cons y l₂ ih₂ =>
          rw [mergeListAgg]
          rw [mergeAuxList]
          split_ifs
          case pos =>
            simp [List.length_cons]
            sorry
          case neg => sorry

theorem sort_equal_length {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : ∀ l, (sort r l).length = l.length) :
  ∀ l l₁ l₂, l₁ ++ l₂ = l → (mergeListAgg r (sort r l₁) (sort r l₂)).length = l.length :=
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [merge_equal_length]
    have h₁ : (sort r l₁).length = l₁.length := h l₁
    have h₂ : (sort r l₂).length = l₂.length := h l₂
    simp [List.length_append]
    rw [←h₁, ←h₂]

end SortTR
