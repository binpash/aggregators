import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

namespace SortTR

/-- `mergeListAgg` preserves the base case `[]` -/
lemma merge_base_case {α : Type} (r : α → α → Bool) : mergeListAgg r [] [] = [] :=
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

--lemma merge_communicative_length :
--  ∀ l₁ l₂, (mergeListAgg r l₁ l₂) = (mergeListAgg r l₂ l₁) := sorry

/-- `mergeAuxList` preserves length -/
lemma mergeAux_length :
  ∀ acc l₁ l₂, (mergeAuxList acc r l₁ l₂).length
    = acc.length + (l₁ ++ l₂).length :=
  by
    intro acc l₁ l₂
    induction l₁ generalizing acc l₂ with
    | nil =>
      induction l₂ generalizing acc with
        | nil =>
          rw [mergeAuxList]
          simp
        | cons y l₂ ih =>
          rw [mergeAuxList]
          simp
    | cons x l₁ ih =>
      induction l₂ generalizing acc with
        | nil =>
          rw [mergeAuxList]
          simp
          aesop
        | cons y l₂ ih₂ =>
          rw [mergeAuxList]
          split_ifs with hxy
          case pos =>
            specialize ih (x :: acc) (y :: l₂)
            simp [ih]
            linarith
          case neg =>
            specialize ih₂ (y :: acc)
            simp [ih₂]
            linarith

/-- `mergeListAgg` preserves length -/
lemma merge_equal_length : ∀ l₁ l₂, (mergeListAgg r l₁ l₂).length = (l₁ ++ l₂).length :=
  by
    intro l₁ l₂
    rw [mergeListAgg]
    rw [mergeAux_length]
    simp

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

/-- `mergeListAgg` preserves membership -/
lemma merge_membership {α : Type} (r : α → α →  Bool) :
  ∀ l₁ l₂, ∀ line ∈ (mergeListAgg r l₁ l₂), line ∈ l₁ ++ l₂ :=
  by
    sorry

theorem sort_membership {α : Type} (sort : (α → α → Bool) → List α → List α)
  (r : α → α → Bool) (h : ∀ lines, ∀ line ∈ (sort r lines), line ∈ lines) :
  ∀ lines l₁ l₂, l₁ ++ l₂ = lines →
    ∀ line ∈ (mergeListAgg r (sort r l₁) (sort r l₂)), line ∈ lines :=
  by
    intro lines l₁ l₂ hsplit line hline
    rw [←hsplit]
    have hm := merge_membership r (sort r l₁) (sort r l₂) line hline
    rw [List.mem_append] at hm
    cases hm with
    | inl hsort =>
      have hinl := h l₁ line hsort
      simp [hinl]
    | inr hsort =>
      have hinl := h l₂ line hsort
      simp [hinl]

end SortTR
