import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/- Unlike `Verification/Sort.lean`, this file is for the tail-recursive implementation of `sort` -/

/-- List-based tail recursive implementation from Atoms.lean -/
def mergeAuxListTR (acc : List α) (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => acc.reverse ++ ys
  | xs, [] => acc.reverse ++ xs
  | x :: xs, y :: ys =>
    if le x y then
      mergeAuxListTR (x::acc) le xs (y :: ys)
    else
      mergeAuxListTR (y::acc) le (x :: xs) ys

def mergeListTR (le : α → α → Bool) (xs ys : List α) : List α :=
  mergeAuxListTR [] le xs ys

theorem merge_base_case_tr {α : Type} (r : α → α → Bool) : mergeListTR r [] [] = [] :=
  by
    rw [mergeListTR]
    rw [mergeAuxListTR]
    apply List.reverse_nil

theorem sort_base_case_tr {α : Type}
  (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : sort r [] = []) :
  (mergeListTR r (sort r []) (sort r [])) = [] :=
  by
    rw [h, merge_base_case_tr]

lemma merge_equal_length_tr : ∀ l₁ l₂, (mergeListTR r l₁ l₂).length = (l₁ ++ l₂).length :=
  by
    intro l₁ l₂
    induction l₁ generalizing l₂ with
    | nil =>
      rw [mergeListTR]
      rw [mergeAuxListTR]
      simp only [List.reverse_nil, List.nil_append]
    | cons x l₁ ih =>
      induction l₂ with
        | nil =>
          rw [mergeListTR]
          rw [mergeAuxListTR]
          simp [List.length_cons]
          simp [List.append_nil]
        | cons y l₂ ih₂ =>
          rw [mergeListTR]
          rw [mergeAuxListTR]
          split_ifs
          case pos =>
            simp [List.length_cons]
            sorry
          case neg => sorry

theorem sort_equal_length_tr {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : ∀ l, (sort r l).length = l.length) :
  ∀ l l₁ l₂, l₁ ++ l₂ = l → (mergeListTR r (sort r l₁) (sort r l₂)).length = l.length :=
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [merge_equal_length_tr]
    have h₁ : (sort r l₁).length = l₁.length := h l₁
    have h₂ : (sort r l₂).length = l₂.length := h l₂
    simp [List.length_append]
    rw [←h₁, ←h₂]
