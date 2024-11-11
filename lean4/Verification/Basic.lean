import Mathlib
import Mathlib.Data.List.Sort 
import Lean
open Lean Elab Meta

/- 
  The wc command counts the number of characters in a file.
  The wc_agg function is a simple aggregation function that sums the number of characters in two files.
-/

def wc_agg : Nat → Nat → Nat :=
  λ x y ↦ x + y

-- wc xs + wc ys = wc ys + wc xs

theorem wc_correctness 
  (wc : String → Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = wc xs + wc ys) : 
  wc (xs ++ ys) = wc_agg (wc xs) (wc ys) :=
  by 
    rw [wc_agg]
    rw [h]

def pairwise_add : Nat × Nat → Nat × Nat → Nat × Nat
  := λ (x1, y1) (x2, y2) => (x1 + x2, y1 + y2)

def wc_agg' := pairwise_add

theorem wc_correctness' (wc : String → Nat × Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = pairwise_add (wc xs) (wc ys)) : 
  wc (xs ++ ys) = wc_agg' (wc xs) (wc ys) :=
  by
    rw [wc_agg']
    rw [h]

/-
def wc : String → Nat :=

  λ file ↦ file.length

def length : (@& String) → Nat
  ⟨s⟩ => s.length

def append : String → (@& String) → String
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

theorem wc_correctness (xs ys : String) : 
wc (xs ++ ys) = wc_agg (wc xs) (wc ys) := 
  by 
    rw [wc_agg]
    repeat rw [wc]
    -- 1. simp [length]
    -- 2. simp [append]
    -- 3. simp [List.length_append]
    apply String.length_append
-/

/-
  The sort command sorts a list of strings.
  The sort_agg function is a simple aggregation function that merges the two sorted lists.
-/

-- REFERENCE: 
-- https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/Data/List/Sort.lean

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

def merge {α : Type} (r : α → α → Prop) [DecidableRel r] 
  : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if (r a b) then a :: merge r l (b :: l') else b :: merge r (a :: l) l'

def mergeSort (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `mergeSort_cons_cons` proof easier
    let ls := (split (a :: b :: l))
    have e : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
    have h := length_split_lt e
    have := h.1
    have := h.2
    exact merge r (mergeSort r ls.1) (mergeSort r ls.2)
  termination_by l => length l

-- This is mergeSort_cons_cons from the mathlib library

alias sort := mergeSort 
alias sort_agg := merge

theorem sort_correctness {a b} {c xs ys : List α} 
    (r : α → α → Prop) [DecidableRel r] (h : split (a :: b :: c) = (xs, ys)) :
    sort r (a :: b :: c) = sort_agg r (sort r xs) (sort r ys) := by

  rw [sort, sort_agg]
  simp only [mergeSort, h]

/-
  The grep command searches for a pattern in a file.
  The grep_agg function is a simple aggregation function that concatenates the results of two greps.
-/

def grep_agg : String → String → String :=
  λ x y ↦ x ++ y

theorem grep_correctness (grep : String → Strinig → String) 
  (h : ∀ xs ys pattern, grep (xs ++ ys) pattern = grep xs pattern ++ grep ys pattern)
  (xs ys : String) : 
  grep (xs ++ ys) pattern = grep_agg (grep xs pattern) (grep ys pattern) :=
  by
    rw [grep_agg]
    rw [h]

/-
  The uniq command removes duplicates from a list of strings.
  The unique_agg function is a simple aggregation function that merges the two unique lists.
-/

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

-- TODO: Specify the optimized uniq_agg function 
-- def uniq_agg {α : Type} [DecidableEq α] : List α → List α → List α :=
--   sorry
