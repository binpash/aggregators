import Mathlib
import Mathlib.Data.List.Sort 
import Lean
open Lean Elab Meta

/- 
  The wc command counts the number of characters in a file.
  The wc_agg function is a simple aggregation function that sums the number of characters in two files.
-/

def sum : Nat → Nat → Nat :=
  λ x y ↦ x + y

theorem wc_correctness 
  (wc : String → Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = wc xs + wc ys) : 
  wc (xs ++ ys) = sum (wc xs) (wc ys) :=
  by 
    rw [sum]
    rw [h]

def pairwise_sum : Nat × Nat → Nat × Nat → Nat × Nat
  := λ (x1, y1) (x2, y2) => (x1 + x2, y1 + y2)

theorem wc_correctness' (wc : String → Nat × Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys)) : 
  wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys) :=
  by
    rw [h]

def triple_sum : Nat × Nat × Nat → Nat × Nat × Nat → Nat × Nat × Nat
  := λ (x1, y1, z1) (x2, y2, z2) => (x1 + x2, y1 + y2, z1 + z2)

def is_substring (substr str : String) : Prop :=
  ∃ xs ys : String, str = xs ++ substr ++ ys

theorem wc_ordering (wc : String → Nat × Nat × Nat) 
  (h: ∀ s₁ s₂, is_substring s₂ s₁ → wc s₁ >= wc s₂) : 
  ∀ s₁ s₂ a b c d, 
    is_substring s₂ s₁ → 
    s₁ = a ++ b → 
    s₂ = c ++ d → 
    triple_sum (wc a) (wc b) >= triple_sum (wc c) (wc d) := 
  by
    intro s₁ s₂ a b c d hsubstr hsplit1 hsplit2
    -- have hwc : wc s₁ ≥ wc s₂ := h s₁ s₂ hsubstr
    -- rw [hsplit1, hsplit2] at hwc
    -- obtain ⟨xs, ys, hconcat⟩ := hsubstr
    -- rw [hconcat] at hsplit1

    -- Is this necessarily true?
    have hwc2 : wc a + wc b ≥ wc c + wc d := 
      by
        sorry
    
    rw [triple_sum]
    rw [triple_sum]
    apply hwc2

theorem wc_ordering2 (wc : String → Nat × Nat × Nat) 
  (h : ∀ s s₁ s₂, s = s₁ ++ s₂ → wc s = wc s₁ + wc s₂) :
  ∀ s s₁ s₂ a b c d, 
    s = s₁ ++ s₂ →
    s₁ = a ++ b → 
    s₂ = c ++ d → 
    triple_sum (wc s₁) (wc s₂) = triple_sum (wc (a ++ b)) (wc (c ++ d)) := 
  by 
    intro s s₁ s₂ a b c d hsplit hsplit1 hsplit2
    -- have h_s₁ : wc s₁ = wc a + wc b := h s₁ a b hsplit1
    -- have h_s₂ : wc s₂ = wc c + wc d := h s₂ c d hsplit2
    -- rw [triple_sum]
    -- rw [h_s₁, h_s₂]
    -- rw [triple_sum]
    -- subst hsplit hsplit2 hsplit1
    simp_all only

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

def merge {α : Type} (r : α → α → Bool)
  : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if (r a b) then a :: merge r l (b :: l') else b :: merge r (a :: l) l'

def mergeSort (r : α → α → Bool) : List α → List α
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

theorem sort_correctness {a b} {c xs ys : List α} (r : α → α → Bool)
    (h : split (a :: b :: c) = (xs, ys)) :
    mergeSort r (a :: b :: c) = merge r (mergeSort r xs) (mergeSort r ys) := 
  by
  simp only [mergeSort, h]


/- In sort, length is the same as the length of the sorted input -/

theorem merge_equal_length : ∀ l₁ l₂, (merge r l₁ l₂).length = (l₁ ++ l₂).length := 
  by
    intro l₁ l₂
    induction l₁ generalizing l₂ with 
      | nil => 
        rw [merge]
        rw [List.nil_append]
      | cons x l₁ ih => 
        induction l₂ with
          | nil =>
            rw [merge]
            simp [List.length_cons] 
            simp [List.append_nil]
          | cons y l₂ ih₂ => 
            rw [merge]
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
  ∀ l l₁ l₂, l₁ ++ l₂ = l → (merge r (sort r l₁) (sort r l₂)).length = l.length := 
  by
    intro l l₁ l₂ hl
    rw [←hl]
    rw [List.length_append]
    rw [merge_equal_length]
    have h₁ : (sort r l₁).length = l₁.length := h l₁
    have h₂ : (sort r l₂).length = l₂.length := h l₂
    rw [←h₁, ←h₂]
    rw [List.length_append]

/-
  The grep command searches for a pattern in a file.
  The grep_agg function is a simple aggregation function that concatenates the results of two greps.
-/

def concat : String → String → String :=
  λ x y ↦ x ++ y

theorem concat_correctness 
  (f : String → String) 
  (xs ys : String) 
  (h : ∀ xs ys, f (xs ++ ys) = f xs ++ f ys) : 
  f (xs ++ ys) = concat (f xs) (f ys) :=
  by
    rw [concat]
    rw [h]

-- Cat is just a function that concatenates two strings
theorem cat_size
  (cat : String → String)
  (h : ∀ s xs ys, s = xs ++ ys → cat s = cat xs ++ cat ys) : 
  ∀ s xs ys a b c d, 
    s = xs ++ ys → 
    xs = a ++ b →
    ys = c ++ d →
    concat (cat xs) (cat ys) = concat (cat a) (cat b) ++ concat (cat c) (cat d) := 
  by
    intro s xs ys a b c d a_1 a_2 a_3
    subst a_3 a_1 a_2
    simp_all only
    rfl

def concat_list : List String → List String → List String :=
  λ xs ys ↦ xs ++ ys

-- The only difference between concat and grep is that grep has a pattern argument
-- And the input is a list of strings instead of a single string
theorem grep_correctness 
  (grep : List String → String → List String) 
  (xs ys : List String) 
  (h : ∀ xs ys pattern, grep (xs ++ ys) pattern = grep xs pattern ++ grep ys pattern) : 
  grep (xs ++ ys) pattern = concat_list (grep xs pattern) (grep ys pattern) :=
  by
    rw [concat_list]
    rw [h]

-- The output is smaller than the input
theorem grep_size
  (grep: List String → String → List String)
  (h: ∀ str pattern, (grep str pattern).length <= str.length) :
  ∀ str pattern, 
    ∀ a b, str = a ++ b → 
    (concat_list (grep a pattern) (grep b pattern)).length <= str.length := 
  by
    intro s pattern a b hsplit
    rw [concat_list]
    rw [hsplit]
    have h₁ := h a pattern
    have h₂ := h b pattern
    simp [String.length_append]
    exact Nat.add_le_add h₁ h₂

-- Membership is preserved
theorem grep_contains
  (grep: List String → String → List String)
  (h: ∀ lines pattern, ∀ line ∈ (grep lines pattern), line ∈ lines) :
  ∀ lines pattern, 
    ∀ a b, lines = a ++ b → 
      ∀ line ∈ (concat_list (grep a pattern) (grep b pattern)), line ∈ lines := 
  by
    intro lines pattern a b hsplit line
    rw [concat_list]
    rw [hsplit]
    intro hin
    subst hsplit
    simp_all only [List.mem_append]
    cases hin with
    | inl h1 =>
      apply Or.inl
      apply h
      exact h1
    | inr h2 =>
      apply Or.inr
      apply h
      exact h2

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
