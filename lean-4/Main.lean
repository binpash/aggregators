import Lean
import Mathlib.Data.List.Sort
open Lean Elab Meta

/- 
  The wc command counts the number of characters in a file.
  The wc_agg function is a simple aggregation function that sums the number of characters in two files.
-/

def wc_agg : Nat → Nat → Nat :=
  λ x y ↦ x + y

theorem wc_correctness (wc : String → Nat) 
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

def sort_agg {α : Type} (r : α → α → Bool) (xs ys : List α) := 
  List.merge r xs ys

def sort_correctness {α : Type} (sort : (α → α → Bool) → List α → List α) 
  (r : α → α → Bool) (xs ys : List α) :
  sort r (xs ++ ys) = sort_agg r (sort r xs) (sort r ys) :=
  by
    rw [sort_agg]
    sorry

/-
def sort {α : Type} (r : α → α → Prop) [DecidableRel r] := List.mergeSort r

theorem sort_sort {α : Type} (r : α → α → Prop) (xs : List α) [DecidableRel r] : 
  sort r (sort r xs) = sort r xs :=
  by
    rw [sort]
    sorry

theorem sort_correctness (xs ys : List String) (r : String → String → Prop) [DecidableRel r] :
  sort r (xs ++ ys) = sort_agg r (sort r xs) (sort r ys) := 
  by
    rw [sort_agg]
    repeat rw [sort]
    sorry
-/

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
  λ xs ↦ xs.eraseDups

-- Run uniq again to remove duplicates from the concatenated list
def uniq_uniq {α : Type} [DecidableEq α] (xs ys: List α) : 
  uniq (xs ++ ys) = uniq (uniq xs ++ uniq ys) :=
  by
    repeat rw [uniq]
    sorry

-- TODO: Specify the optimized uniq_agg function 
-- def uniq_agg {α : Type} [DecidableEq α] : List α → List α → List α :=
--   sorry
