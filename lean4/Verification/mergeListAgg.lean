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

/-- `mergeListAgg` preserves membership -/
lemma merge_membership {α : Type} (r : α → α →  Bool) :
  ∀ l₁ l₂, ∀ line ∈ (mergeListAgg r l₁ l₂), line ∈ l₁ ++ l₂ :=
  by
    sorry

namespace MergeListAggExample 

opaque α : Type
opaque foo : (α → α → Bool) → List α → List α
opaque r : α → α → Bool

axiom foo_base_case : foo r [] = []
axiom foo_equal_length : ∀ l, (foo r l).length = l.length
axiom foo_membership : ∀ lines, ∀ line ∈ (foo r lines), line ∈ lines 

theorem parallel_foo_base_case : mergeListAgg r (foo r []) (foo r []) = [] :=
  by
    rw [foo_base_case, merge_base_case]

theorem parallel_foo_equal_length : ∀ l l₁ l₂, l₁ ++ l₂ = l → 
(mergeListAgg r (foo r l₁) (foo r l₂)).length = l.length :=
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [merge_equal_length]
    have h₁ : (foo r l₁).length = l₁.length := foo_equal_length l₁
    have h₂ : (foo r l₂).length = l₂.length := foo_equal_length l₂
    simp [List.length_append]
    rw [←h₁, ←h₂]

theorem parallel_foo_membership :
  ∀ lines l₁ l₂, l₁ ++ l₂ = lines →
    ∀ line ∈ (mergeListAgg r (foo r l₁) (foo r l₂)), line ∈ lines :=
  by
    intro lines l₁ l₂ hsplit line hline
    rw [←hsplit]
    have hm := merge_membership r (foo r l₁) (foo r l₂) line hline
    rw [List.mem_append] at hm
    cases hm with
    | inl hfoo =>
      have hinl := foo_membership l₁ line hfoo
      simp [hinl]
    | inr hfoo =>
      have hinl := foo_membership l₂ line hfoo
      simp [hinl]

end MergeListAggExample
end SortTR
