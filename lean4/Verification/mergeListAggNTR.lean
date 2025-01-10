import Synthesis.Atoms
import Init.Data.List.Sort
import Init.Data.List.Perm
import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Lean
open Lean Elab Meta

namespace SortNTR

/-- `mergeListAggNTR` preserves the base case `[]` -/
lemma merge_base_case {α : Type} (r : α → α → Bool) :
  mergeListAggNTR r [] [] = [] :=
  by
    rw [mergeListAggNTR]

/-- `mergeListAggNTR` preserves length -/
lemma merge_equal_length : ∀ l₁ l₂,
  (mergeListAggNTR r l₁ l₂).length = (l₁ ++ l₂).length :=
  by
    intro l₁ l₂
    induction l₁ generalizing l₂ with
    | nil =>
      rw [mergeListAggNTR]
      rw [List.nil_append]
    | cons x l₁ ih =>
      induction l₂ with
      | nil =>
        rw [mergeListAggNTR]
        simp [List.length_cons]
        simp [List.append_nil]
      | cons y l₂ ih₂ =>
        rw [mergeListAggNTR]
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

/-- `mergeListAggNTR` preserves membership -/
lemma merge_membership {α : Type} (r : α → α →  Bool) :
  ∀ l₁ l₂, ∀ line ∈ (mergeListAggNTR r l₁ l₂), line ∈ l₁ ++ l₂ :=
  by
    intro l₁ l₂ line hline
    induction l₁ generalizing l₂ with
    | nil =>
      rw [mergeListAggNTR] at hline
      rw [List.nil_append]
      exact hline
    | cons x l₁ ih =>
      induction l₂ with
      | nil =>
        rw [mergeListAggNTR] at hline
        simp_all only [List.mem_append, List.mem_cons, List.append_nil]
        simp only [reduceCtorEq, imp_self]
      | cons y l₂ ih₂ =>
        rw [mergeListAggNTR] at hline
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

/-- `mergeListAggNTR` preserves multiset property -/
lemma merge_multiset {α : Type} (r : α → α →  Bool) :
  ∀ l₁ l₂, (Multiset.ofList (mergeListAggNTR r l₁ l₂)) = (Multiset.ofList (l₁ ++ l₂)) :=
  by
    intro l₁ l₂
    rw [Multiset.coe_eq_coe]
    induction l₁ generalizing l₂ with
    | nil =>
      rw [mergeListAggNTR]
      rw [List.nil_append]
    | cons x xs ih =>
      induction l₂ with
      | nil =>
        rw [mergeListAggNTR]
        rw [List.append_nil]
        intro hlist
        simp_all only [reduceCtorEq]
      | cons y ys ih₂ =>
        rw [mergeListAggNTR]
        split_ifs
        case pos =>
          rw [List.cons_append]
          rw [List.perm_cons]
          exact ih (y :: ys)
        case neg =>
          have hperm1 : (y :: (mergeListAggNTR r (x :: xs) ys)).Perm (y :: (x :: xs ++ ys) ) :=
            by
              rw [List.cons_append]
              rw [List.perm_cons]
              exact ih₂
          have hperm2 : (y :: (x :: xs ++ ys)).Perm (x :: (xs ++ y :: ys)) :=
            by
              sorry
          exact hperm1.trans hperm2

/-- `mergeListAggNTR` preserves the permutation property. 
     This is the same as the multiset property above. -/
lemma merge_perm {α : Type} (r : α → α →  Bool) :
  ∀ l₁ l₂, (mergeListAggNTR r l₁ l₂).Perm (l₁ ++ l₂) :=
  by
    intro l₁ l₂
    have h := merge_multiset r l₁ l₂
    rw [Multiset.coe_eq_coe] at h
    exact h

lemma merge_ordering (r : α → α → Bool) :
  ∀ a b c d, List.Sublist (a ++ b) (c ++ d) →
    List.Sublist (mergeListAggNTR r a b) (mergeListAggNTR r c d) :=
  by
    intro a b c d hsublist
    sorry

inductive Sorted (r : α → α → Bool) : List α → Prop
  | nil : Sorted r []
  | cons : ∀ {a : α} {l : List α}, (∀ a', a' ∈ l → r a a') → Sorted r l → Sorted r (a :: l)

/- Taken from Mathlib.Data.List.Sort -/
lemma eq_of_perm_of_sorted {r : α → α → Bool} {l₁ l₂ : List α} 
  (hp : l₁.Perm l₂) (hs₁ : Sorted r l₁) (hs₂ : Sorted r l₂) 
  : l₁ = l₂ := by sorry

/- merge preserves sorted -/
lemma merge_sorted {r : α → α → Bool} {l₁ l₂ : List α} (hl₁ : Sorted r l₁) (hl₂ : Sorted r l₂) : 
  Sorted r (mergeListAggNTR r l₁ l₂) := by 
  induction l₁ generalizing l₂ with
  | nil =>
    rw [mergeListAggNTR]
    exact hl₂
  | cons x xs ih => 
    induction l₂ with
    | nil =>
      rw [mergeListAggNTR]
      exact hl₁
      intro _
      simp_all only [reduceCtorEq]
    | cons y ys ih₂ => 
      rw [mergeListAggNTR]
      split_ifs
      case pos hpos =>
        apply Sorted.cons
        intro a ha
        simp at ha
        sorry
        sorry

      case neg hneg =>
        apply Sorted.cons
        intro a ha
        simp at ha
        sorry
        sorry

/- If sort l₁ is equal to sort l₂, then merging the partials of sort l₁ is equal to merging the partials of sort l₂. This does not hold if sort x = "ab" -/
lemma merge_equality : ∀ a b c d, a ++ b = c ++ d → mergeListAggNTR r a b = mergeListAggNTR r c d := sorry

-- Sort Examples
namespace MergeListAggNTRExample

-- Define opaque types and axioms
opaque α : Type
opaque r : α → α → Bool
opaque foo : (α → α → Bool) → List α → List α

axiom foo_base_case : foo r [] = []
axiom foo_equal_length : ∀ l, (foo r l).length = l.length
axiom foo_membership :  ∀ lines, ∀ line ∈ (foo r lines), line ∈ lines
axiom foo_multiset : ∀ l, (Multiset.ofList (foo r l)) = (Multiset.ofList l)
axiom foo_perm : ∀ l, (foo r l).Perm l
axiom foo_sorted : ∀ l, Sorted r (foo r l)
axiom foo_ordering : ∀ l₁ l₂, List.Sublist l₁ l₂ → List.Sublist (foo r l₁) (foo r l₂)

theorem parallel_foo_base_case : (mergeListAggNTR r (foo r []) (foo r [])) = [] :=
  by
    rw [foo_base_case, merge_base_case]

theorem parallel_foo_equal_length : ∀ l l₁ l₂, l₁ ++ l₂ = l → 
(mergeListAggNTR r (foo r l₁) (foo r l₂)).length = l.length :=
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [List.length_append]
    rw [merge_equal_length]
    have h₁ : (foo r l₁).length = l₁.length := foo_equal_length l₁
    have h₂ : (foo r l₂).length = l₂.length := foo_equal_length l₂
    simp [List.length_append]
    rw [←h₁, ←h₂]

theorem parallel_foo_membership : ∀ lines l₁ l₂, l₁ ++ l₂ = lines →
∀ line ∈ (mergeListAggNTR r (foo r l₁) (foo r l₂)), line ∈ lines :=
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

/- `foo` preserves the multiset property -/
theorem parallel_foo_multiset : ∀ l l₁ l₂, l₁ ++ l₂ = l →
(Multiset.ofList (mergeListAggNTR r (foo r l₁) (foo r l₂))) = (Multiset.ofList l) :=
  by
    intro l l₁ l₂ hsplit
    rw [←hsplit]
    rw [merge_multiset]
    have h₁ := foo_multiset l₁
    have h₂ := foo_multiset l₂
    rw [Multiset.coe_eq_coe] at h₁ h₂
    rw [Multiset.coe_eq_coe]
    exact List.Perm.append h₁ h₂

theorem parallel_foo_perm : ∀ l l₁ l₂, l₁ ++ l₂ = l →
(mergeListAggNTR r (foo r l₁) (foo r l₂)).Perm l :=
  by
    intro l l₁ l₂ hsplit
    rw [←hsplit]
    have h₁ := foo_perm l₁
    have h₂ := foo_perm l₂
    apply (merge_perm r (foo r l₁) (foo r l₂)).trans
    apply List.Perm.append h₁ h₂

/-- If l₁ is a sublist of l₂, then foo l₁ is a sublist of foo l₂ -/
theorem parallel_foo_ordering :
  ∀ l₁ l₂, List.Sublist l₁ l₂ →
    ∀ a b c d, l₁ = a ++ b → l₂ = c ++ d →
      List.Sublist
        (mergeListAggNTR r (foo r a) (foo r b))
        (mergeListAggNTR r (foo r c) (foo r d)) :=
    by
      intro l₁ l₂ hsublist a b c d hsplit₁ hsplit₂
      apply merge_ordering r (foo r a) (foo r b) (foo r c) (foo r d)
      have hl := foo_ordering l₁ l₂ hsublist
      rw [hsplit₁, hsplit₂] at hl
      sorry

theorem parallel_foo_sorted :
  ∀ l l₁ l₂, l₁ ++ l₂ = l →
    Sorted r (mergeListAggNTR r (foo r l₁) (foo r l₂)) :=
  by
    intro l l₁ l₂ hsplit
    have h₁ := foo_sorted l₁
    have h₂ := foo_sorted l₂
    exact merge_sorted h₁ h₂

/- If foo applied twice is itself, then mergeListAggNTR applied twice is itself
   This does not hold for if foo x = "ab" -/
theorem parallel_foo_idempotence :
  ∀ l a b c d, a ++ b = l →
    c ++ d = (mergeListAggNTR r (foo r a) (foo r b)) →
    (mergeListAggNTR r (foo r a) (foo r b)) =
    (mergeListAggNTR r (foo r c) (foo r d)) :=
  by
    intro l a b c d hsplit₁ hsplit₂ 
    have hsab := merge_sorted (foo_sorted a) (foo_sorted b)
    have hscd := merge_sorted (foo_sorted c) (foo_sorted d) 
    have hp : (mergeListAggNTR r (foo r a) (foo r b)).Perm (mergeListAggNTR r (foo r c) (foo r d)) := 
      by
        apply (merge_perm r (foo r a) (foo r b)).trans
        apply List.Perm.symm
        apply (merge_perm r (foo r c) (foo r d)).trans
        apply (List.Perm.append (foo_perm c) (foo_perm d)).trans
        apply List.Perm.symm 
        apply (List.Perm.append (foo_perm a) (foo_perm b)).trans
        have hpabcd : (a ++ b).Perm (c ++ d) := by
          rw [hsplit₂]
          apply List.Perm.symm 
          apply (merge_perm r (foo r a) (foo r b)).trans
          apply List.Perm.append (foo_perm a) (foo_perm b)
        exact hpabcd
    exact eq_of_perm_of_sorted hp hsab hscd

theorem foo_equality (l₁ l₂ : List α) (h: foo r l₁ = foo r l₂) :
  ∀ a b c d, l₁ = a ++ b → l₂ = c ++ d →
    mergeListAggNTR r (foo r a) (foo r b) = mergeListAggNTR r (foo r c) (foo r d) :=
    by
      intro a b c d hl₁ hl₂
      rw [hl₁, hl₂] at h
      sorry

end MergeListAggNTRExample

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
def mergeListAggNTR {α : Type} (r : α → α → Bool)
  : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if (r a b) then a :: mergeListAggNTR r l (b :: l') else b :: mergeListAggNTR r (a :: l) l'
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
    exact mergeListAggNTR r (merge_sort r ls.1) (merge_sort r ls.2)
  termination_by l => length l

-- This is merge_sort_cons_cons from the mathlib library
theorem sort_correctness {a b} {c xs ys : List α} (r : α → α → Bool)
    (h : split (a :: b :: c) = (xs, ys)) :
    merge_sort r (a :: b :: c) = mergeListAggNTR r (merge_sort r xs) (merge_sort r ys) :=
  by
  simp only [merge_sort, h]

end SortNTR
