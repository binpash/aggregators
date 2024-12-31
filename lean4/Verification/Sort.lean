import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

-- NOTE: these proofs only apply to the non-tail recursive `merge_sort_ntr`

namespace SortNTR

/-- `merge_agg_ntr` preserves the base case `[]` -/
lemma merge_base_case {α : Type} (r : α → α → Bool) : merge_agg_ntr r [] [] = [] :=
  by
    rw [merge_agg_ntr]

theorem sort_base_case {α : Type}
  (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : sort r [] = []) :
  (merge_agg_ntr r (sort r []) (sort r [])) = [] :=
  by
    rw [h, merge_base_case]

/-- `merge_agg_ntr` preserves length -/
lemma merge_equal_length : ∀ l₁ l₂, (merge_agg_ntr r l₁ l₂).length = (l₁ ++ l₂).length :=
  by
    intro l₁ l₂
    induction l₁ generalizing l₂ with
    | nil =>
      rw [merge_agg_ntr]
      rw [List.nil_append]
    | cons x l₁ ih =>
      induction l₂ with
      | nil =>
        rw [merge_agg_ntr]
        simp [List.length_cons]
        simp [List.append_nil]
      | cons y l₂ ih₂ =>
        rw [merge_agg_ntr]
        split_ifs
        case pos =>
          simp [List.length_cons]
          rw [ih]
          simp [List.length_append]
        case neg =>
          simp [List.length_cons]
          rw [ih₂]
          simp
          rw [add_assoc]

theorem sort_equal_length {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : ∀ l, (sort r l).length = l.length) :
  ∀ l l₁ l₂, l₁ ++ l₂ = l → (merge_agg_ntr r (sort r l₁) (sort r l₂)).length = l.length :=
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [List.length_append]
    rw [merge_equal_length]
    have h₁ : (sort r l₁).length = l₁.length := h l₁
    have h₂ : (sort r l₂).length = l₂.length := h l₂
    simp [List.length_append]
    rw [←h₁, ←h₂]

/-- `merge_agg_ntr` preserves membership -/
lemma merge_membership {α : Type} (r : α → α →  Bool) : ∀ l₁ l₂, ∀ line ∈ (merge_agg_ntr r l₁ l₂), line ∈ l₁ ++ l₂ :=
  by
    intro l₁ l₂ line hline
    induction l₁ generalizing l₂ with
    | nil =>
      rw [merge_agg_ntr] at hline
      rw [List.nil_append]
      exact hline
    | cons x l₁ ih =>
      induction l₂ with
      | nil =>
        rw [merge_agg_ntr] at hline
        simp_all only [List.mem_append, List.mem_cons, List.append_nil]
        simp only [reduceCtorEq, imp_self]
      | cons y l₂ ih₂ =>
        rw [merge_agg_ntr] at hline
        split_ifs at hline
        case pos =>
          simp at hline
          cases hline with
          | inl hx => simp [hx]
          | inr hm =>
            have hy := ih (y :: l₂) hm
            simp [hy]
        case neg =>
          simp at hline
          cases hline with
          | inl hy => simp [hy]
          | inr hm =>
            have hx := ih₂ hm
            aesop

theorem sort_membership {α : Type} (sort : (α → α → Bool) → List α → List α)
  (r : α → α → Bool) (h : ∀ lines, ∀ line ∈ (sort r lines), line ∈ lines) :
  ∀ lines l₁ l₂, l₁ ++ l₂ = lines → ∀ line ∈ (merge_agg_ntr r (sort r l₁) (sort r l₂)), line ∈ lines :=
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

theorem sort_ordering {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (l₁ l₂ : List α) (h: ∀ l₁ l₂, List.Sublist l₁ l₂ → List.Sublist (sort r l₁) (sort r l₂)) :
  ∀ l₁ l₂, List.Sublist l₁ l₂ → ∀ a b c d, a ++ b = l₁ → c ++ d = l₂ → List.Sublist (merge_agg_ntr r (sort r a) (sort r b)) (merge_agg_ntr r (sort r c) (sort r d)) :=
    by
      intro l₁ l₂ hsublist a b c d hsplit₁ hsplit₂
      sorry

theorem sort_equality {α : Type} (sort : (α → α → Bool) → List α → List α)
  (r : α → α → Bool) (l₁ l₂ : List α) (h: sort r l₁ = sort r l₂) :
  ∀ a b c d, a ++ b = l₁ → c ++ d = l₂ → merge_agg_ntr r (sort r a) (sort r b) = merge_agg_ntr r (sort r c) (sort r d) :=
    by
      intro a b c d hl₁ hl₂
      sorry

/- If sort l₁ is equal to sort l₂, then merging the partials of l₁ is equal to merging the partials of l₂.
   This does not hold if sort x = "ab" -/
theorem sort_stability (l₁ l₂ : List α) (r : α → α → Bool) (sort : (α → α → Bool) → List α → List α)
  (h : sort r l₁ = sort r l₂) :
  ∀ a b c d, a ++ b = l₁ → c ++ d = l₂ → merge_agg_ntr r (sort r a) (sort r b) = merge_agg_ntr r (sort r c) (sort r d) :=
  by
    intro a b c d hsplit1 hsplit2
    rw [←hsplit1, ←hsplit2] at h
    sorry

/- If sort applied twice is itself, then merge_agg_ntr applied twice is itself
   This does not hold for if sort x = "ab" -/
theorem sort_idempotent {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : ∀ l, sort r (sort r l) = sort r l) :
  ∀ l l₁ l₂ l₃ l₄, l₁ ++ l₂ = l → l₃ ++ l₄ =
  (merge_agg_ntr r (sort r l₁) (sort r l₂)) → (merge_agg_ntr r (sort r l₁) (sort r l₂)) = (merge_agg_ntr r (sort r l₃) (sort r l₄)) :=
  by
    intro l l₁ l₂ l₃ l₄ hl₁l₂ hl₃l₄
    sorry

-- Some correctness lemmas for the non-tail recursive `merge_sort` function in `Data.List.Sort`
-- REFERENCE: https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/Data/List/Sort.lean
def length : List α → Nat := List.length

@[simp]
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
    split (a :: l) = (a :: l₂, l₁) := by rw [split, h]

theorem length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    cases' length_split_le e with h₁ h₂
    exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) := by
    cases' e : split l with l₁' l₂'
    injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; substs l₁ l₂
    cases' length_split_le e with h₁ h₂
    exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩

/- Defined in Synthesis/Atoms.lean
def merge_agg_ntr {α : Type} (r : α → α → Bool)
  : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if (r a b) then a :: merge_agg_ntr r l (b :: l') else b :: merge_agg_ntr r (a :: l) l'
-/

def merge_sort (r : α → α → Bool) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `merge_sort_cons_cons` proof easier
    let ls := (split (a :: b :: l))
    have e : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
    have h := length_split_lt e
    have := h.1
    have := h.2
    exact merge_agg_ntr r (merge_sort r ls.1) (merge_sort r ls.2)
  termination_by l => length l

-- This is merge_sort_cons_cons from the mathlib library
theorem sort_correctness {a b} {c xs ys : List α} (r : α → α → Bool)
    (h : split (a :: b :: c) = (xs, ys)) :
    merge_sort r (a :: b :: c) = merge_agg_ntr r (merge_sort r xs) (merge_sort r ys) :=
  by
  simp only [merge_sort, h]

end SortNTR
