import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/- This is the aggregator used in Aggregators/Uniq.lean. It is not tail-recursive.
def uniqAgg (xs ys : List String)  : List String :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniqAgg xs ys
    else x :: uniqAgg xs (y :: ys)
-/

def uniq_agg_base_case : uniqAgg [] [] = [] := by
  rw [uniqAgg]

def uniq_base_case (uniq : List String → List String) (h : uniq [] = []) :
  uniqAgg (uniq []) (uniq []) = [] :=
  by
    rw [h, uniqAgg]

theorem uniq_agg_size : ∀ a b, (uniqAgg a b).length <= a.length + b.length :=
  by
    intro a b
    induction a generalizing b with
      | nil =>
        simp [uniqAgg]
      | cons x xs ih =>
        induction b with
          | nil =>
            simp [uniqAgg]
          | cons y ys ih2 =>
            simp [uniqAgg]
            split_ifs
            case pos =>
              simp [List.length_cons]
              have h := ih ys
              linarith
            case neg =>
              simp only [List.length_cons] at ih
              simp [List.length_cons]
              have h := ih (y :: ys)
              simp [List.length_cons] at h
              linarith

theorem uniq_size (uniq: List String → List String)
  (h: ∀ lines, (uniq lines).length <= lines.length) :
  ∀ lines,
    ∀ a b, lines = a ++ b →
    (uniqAgg (uniq a) (uniq b)).length <= lines.length :=
  by
    intro lines a b hsplit
    have h₁ := h a
    have h₂ := h b
    have h₃ := uniq_agg_size (uniq a) (uniq b)
    rw [hsplit]
    simp [List.length_append]
    calc
      (uniqAgg (uniq a) (uniq b)).length
          ≤ (uniq a).length + (uniq b).length := h₃
      _ ≤ a.length + b.length := by
        apply add_le_add
        exact h₁
        exact h₂
      _ = lines.length := by rw [hsplit, List.length_append]

    subst hsplit
    simp_all only [List.length_append, le_refl]

theorem uniq_agg_membership : ∀ a b, ∀ line ∈ uniqAgg a b, line ∈ a ++ b :=
  by
    intro a b line hin
    induction a generalizing b with
      | nil =>
        simp [uniqAgg] at hin
        exact hin
      | cons x xs ih =>
        induction b with
          | nil =>
            simp [uniqAgg] at hin
            simp [hin]
          | cons y ys ih2 =>
            simp [uniqAgg] at hin
            simp [List.cons_append]
            split_ifs at hin with h_eq
            case pos =>
              subst h_eq
              simp_all only [List.mem_append, List.cons_append, List.mem_cons]
              cases hin with
              | inl h_1 =>
                subst h_1
                simp_all only [true_or, implies_true, or_true, or_self]
              | inr h_1 =>
                simp_all only [or_true, implies_true]
                apply Or.inr
                have g := ih ys h_1
                cases g with
                | inr h_2 =>
                  apply Or.inr
                  apply Or.inr
                  exact h_2
                | inl h_2 =>
                  simp [h_2]
            case neg =>
              simp [List.mem_append] at hin
              cases hin with
              | inl h =>
                  simp [h]
              | inr h =>
                  apply Or.inr
                  have g := ih (y :: ys) h
                  simp_all only [List.mem_append, List.cons_append, List.mem_cons]

-- Membership is preserved
theorem uniq_membership
  (uniq: List String → List String)
  (h: ∀ lines, ∀ line ∈ (uniq lines), line ∈ lines) :
  ∀ lines,
    ∀ a b, lines = a ++ b →
      ∀ line ∈ (uniqAgg (uniq a) (uniq b)), line ∈ lines :=
  by
    intro lines a b hsplit line hin
    rw [hsplit]
    have hcontains := uniq_agg_membership (uniq a) (uniq b) line hin
    cases List.mem_append.1 hcontains with
    | inl huniqa =>
      have ha := h a line huniqa
      simp [List.mem_append]
      apply Or.inl ha
    | inr huniqb =>
      have hb := h b line huniqb
      simp [List.mem_append]
      apply Or.inr hb

/- theorem uniq_idempotence -/
/-   (uniq: List String → List String) -/
/-   (h: ∀ lines, uniq lines = uniq uniq lines) :  -/
/-   ∀ lines,  -/
/-     ∀ a b, lines = a ++ b →  -/
/-       uniq (uniqAgg (uniq a) (uniq b)) = uniqAgg a b := sorry -/

/- Some old work using the actual uniq
def uniq {α : Type} [DecidableEq α] : List α → List α :=
  λ xs ↦ xs.eraseDup

-- Run uniq again to remove duplicates from the concatenated list
def uniq_uniq {α : Type} [DecidableEq α] (xs ys: List α) :
  uniq (xs ++ ys) = uniq (uniq xs ++ uniq ys) :=
  by
    repeat rw [uniq]
    induction xs with
      | nil =>
        repeat rw [List.eraseDup]
        simp
      | cons x xs ih =>
        -- simp [List.eraseDup]
        -- rw [ih]
        sorry

        -- rw [h]
        -- simp [List.eraseDup]
        -- rw [ih]
        -- simp
-/
