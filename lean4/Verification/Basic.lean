import Mathlib
import Mathlib.Data.List.Sort 
import Lean
open Lean Elab Meta

def sum : Nat → Nat → Nat :=
  λ x y ↦ x + y

def pairwise_sum : Nat × Nat → Nat × Nat → Nat × Nat
  := λ (x1, y1) (x2, y2) => (x1 + x2, y1 + y2)

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

theorem wc_correctness 
  (wc : String → Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = wc xs + wc ys) : 
  wc (xs ++ ys) = sum (wc xs) (wc ys) :=
  by 
    rw [sum]
    rw [h]

theorem wc_correctness' (wc : String → Nat × Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys)) : 
  wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys) :=
  by
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

def merge {α : Type} (r : α → α → Bool)
  : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if (r a b) then a :: merge r l (b :: l') else b :: merge r (a :: l) l'

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
    exact merge r (merge_sort r ls.1) (merge_sort r ls.2)
  termination_by l => length l

-- This is merge_sort_cons_cons from the mathlib library

theorem sort_correctness {a b} {c xs ys : List α} (r : α → α → Bool)
    (h : split (a :: b :: c) = (xs, ys)) :
    merge_sort r (a :: b :: c) = merge r (merge_sort r xs) (merge_sort r ys) := 
  by
  simp only [merge_sort, h]

/- Merge preserves length -/
lemma merge_equal_length : ∀ l₁ l₂, (merge r l₁ l₂).length = (l₁ ++ l₂).length := 
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

/- If sort l₁ is equal to sort l₂, then merging the partials of l₁ is equal to merging the partials of l₂ -/
/- This does not hold if sort x = "ab" -/

/- theorem sort_stability (l₁ l₂ : List α) (r : α → α → Bool) (sort : (α → α → Bool) → List α → List α)  -/
/-   (h : sort r l₁ = sort r l₂) : -/
/-   ∀ a b c d, a ++ b = l₁ → c ++ d = l₂ → merge r (sort r a) (sort r b) = merge r (sort r c) (sort r d) := -/
/-   by -/
/-     intro a b c d hsplit1 hsplit2 -/
/-     rw [←hsplit1, ←hsplit2] at h -/
/-     sorry -/

/- If sort applied twice is itself, then merge applied twice is itself
   This does not hold for if sort x = "ab" -/
--
-- Idempotence
theorem sort_idempotent {α : Type} (sort : (α → α → Bool) → List α → List α) (r : α → α → Bool)
  (h : ∀ l, sort r (sort r l) = sort r l) :
  ∀ l l₁ l₂ l₃ l₄, l₁ ++ l₂ = l → l₃ ++ l₄ = 
  (merge r (sort r l₁) (sort r l₂)) → (merge r (sort r l₁) (sort r l₂)) = (merge r (sort r l₃) (sort r l₄)) :=
  by
    intro l l₁ l₂ l₃ l₄ hl₁l₂ hl₃l₄
    sorry

/-
  The grep command searches for a pattern in a file.
  The grep_agg function is a simple aggregation function that concatenates the results of two greps.
-/

def concat_string : String → String → String :=
  λ x y ↦ x ++ y

theorem concat_string_correctness 
  (f : String → String) 
  (xs ys : String) 
  (h : ∀ xs ys, f (xs ++ ys) = f xs ++ f ys) : 
  f (xs ++ ys) = concat_string (f xs) (f ys) :=
  by
    rw [concat_string]
    rw [h]

/- The length of the output after f is less the length of the output after ++ -/
theorem concat_string_ordering_lt (f : String → String → String)
  (h : ∀ xs ys, (f xs ys).length <= (xs ++ ys).length) :
  ∀ xs ys a b c d, 
    xs = a ++ b → 
    ys = c ++ d → 
    (concat_string (f a c) (f b d)).length <= (xs ++ ys).length :=
  by 
    intro xs ys a b c d hsplit hsplit1
    rw [concat_string, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    /- rw [List.length_append] at h₁ -/
    simp [List.length_append]
    simp [List.length_append] at h₁
    simp [List.length_append] at h₂
    linarith

/- The length of the output after f is greater than length of the output after ++ -/
theorem concat_string_ordering_gt (f : String → String → String)
  (h : ∀ xs ys, (f xs ys).length >= (xs ++ ys).length) :
  ∀ xs ys a b c d, 
    xs = a ++ b → 
    ys = c ++ d → 
    (concat_string (f a c) (f b d)).length >= (xs ++ ys).length :=
  by 
    intro xs ys a b c d hsplit hsplit1
    rw [concat_string, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    /- rw [List.length_append] at h₁ -/
    simp [List.length_append]
    simp [List.length_append] at h₁
    simp [List.length_append] at h₂
    linarith

-- Cat is just a function that concatenates two strings
theorem cat_size
  (cat : String → String)
  (h : ∀ s xs ys, s = xs ++ ys → cat s = cat xs ++ cat ys) : 
  ∀ s xs ys a b c d, 
    s = xs ++ ys → 
    xs = a ++ b →
    ys = c ++ d →
    concat_string (cat xs) (cat ys) = concat_string (cat a) (cat b) ++ concat_string (cat c) (cat d) := 
  by
    intro s xs ys a b c d a_1 a_2 a_3
    subst a_3 a_1 a_2
    simp_all only
    rfl

-- The actual Concat function is a ByteArray
def concat_bytearray (acc x : ByteArray) : ByteArray := 
  acc ++ x

theorem concat_bytearray_correctness
  (f : ByteArray → ByteArray) 
  (xs ys : ByteArray) 
  (h : ∀ xs ys, f (xs ++ ys) = f xs ++ f ys) : 
  f (xs ++ ys) = concat_bytearray (f xs) (f ys) :=
  by
    rw [concat_bytearray]
    rw [h]

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
theorem grep_membership
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

def uniq_merge (xs ys : List String)  : List String :=
  match xs, ys with 
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniq_merge xs ys
    else x :: uniq_merge xs (y :: ys)

theorem uniq_merge_size : ∀ a b, (uniq_merge a b).length <= a.length + b.length := 
  by
    intro a b
    induction a generalizing b with
      | nil => 
        simp [uniq_merge]
      | cons x xs ih =>
        induction b with
          | nil =>
            simp [uniq_merge]
          | cons y ys ih2 =>
            simp [uniq_merge]
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
    (uniq_merge (uniq a) (uniq b)).length <= lines.length := 
  by
    intro lines a b hsplit 
    have h₁ := h a
    have h₂ := h b
    have h₃ := uniq_merge_size (uniq a) (uniq b)
    rw [hsplit]
    simp [List.length_append]
    calc
      (uniq_merge (uniq a) (uniq b)).length
          ≤ (uniq a).length + (uniq b).length := h₃
      _ ≤ a.length + b.length := by
        apply add_le_add
        exact h₁
        exact h₂
      _ = lines.length := by rw [hsplit, List.length_append]

    subst hsplit
    simp_all only [List.length_append, le_refl]

theorem uniq_merge_membership : ∀ a b, ∀ line ∈ uniq_merge a b, line ∈ a ++ b := 
  by
    intro a b line hin
    induction a generalizing b with
      | nil => 
        simp [uniq_merge] at hin
        exact hin
      | cons x xs ih =>
        induction b with
          | nil =>
            simp [uniq_merge] at hin
            simp [hin]
          | cons y ys ih2 =>
            simp [uniq_merge] at hin
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
      ∀ line ∈ (uniq_merge (uniq a) (uniq b)), line ∈ lines := 
  by
    intro lines a b hsplit line hin
    rw [hsplit]
    have hcontains := uniq_merge_membership (uniq a) (uniq b) line hin
    cases List.mem_append.1 hcontains with
    | inl huniqa =>
      have ha := h a line huniqa
      simp [List.mem_append]
      apply Or.inl ha
    | inr huniqb =>
      have hb := h b line huniqb
      simp [List.mem_append]
      apply Or.inr hb
