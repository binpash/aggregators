import Mathlib
import Mathlib.Data.List.Sort 
import Lean
open Lean Elab Meta

/-- This is the concat defined in Aggregators/Concat.lean -/
def concat (acc x : ByteArray) : ByteArray := 
  acc ++ x

/- The length of the output after f is less the length of the output after ++ -/
theorem concat_ordering_lt (f : ByteArray → ByteArray → ByteArray)
  (h : ∀ xs ys, (f xs ys).size <= (xs ++ ys).size) :
  ∀ xs ys a b c d, 
    xs = a ++ b → 
    ys = c ++ d → 
    (concat (f a c) (f b d)).size <= (xs ++ ys).size :=
  by 
    intro xs ys a b c d hsplit hsplit1
    rw [concat, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

/- The length of the output after f is greater than the length of the output after ++ -/
theorem concat_ordering_gt (f : ByteArray → ByteArray → ByteArray)
  (h : ∀ xs ys, (f xs ys).size >= (xs ++ ys).size) :
  ∀ xs ys a b c d, 
    xs = a ++ b → 
    ys = c ++ d → 
    (concat (f a c) (f b d)).size >= (xs ++ ys).size :=
  by 
    intro xs ys a b c d hsplit hsplit1
    rw [concat, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

/-- The output of concat is smaller than its input -/
theorem concat_size (f: ByteArray → ByteArray)
  (h: ∀ input, (f input).size <= input.size) :
  ∀ str a b, str = a ++ b → (concat (f a) (f b)).size <= str.size := 
  by
    intro s a b hsplit
    rw [concat]
    rw [hsplit]
    have h₁ := h a
    have h₂ := h b
    simp [ByteArray.size_append]
    exact Nat.add_le_add h₁ h₂

/-- This concat uses List String instead of ByteArray.
    This is necessary because ByteArray does not have membership. -/
def concat_list (acc x : List String) : List String := 
  acc ++ x

/-- Concat preserves membership -/
theorem concat_membership (f: List String → List String) 
  (h : ∀ lines, ∀ line ∈ (f lines), line ∈ lines) : 
  ∀ lines a b, lines = a ++ b → ∀ line ∈ (concat_list (f a) (f b)),  line ∈ lines :=
  by
    intro lines a b hsplit line
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

theorem concat_correctness (f : ByteArray → ByteArray)
  (h : ∀ input xs ys, input = xs ++ ys → f input = f xs ++ f ys) : 
  ∀ input xs ys a b c d, 
    input = xs ++ ys → 
    xs = a ++ b →
    ys = c ++ d →
    concat (f xs) (f ys) = concat (f a) (f b) ++ concat (f c) (f d) := 
  by
    intro input xs ys a b c d hsplit₁ hsplit₂ hsplit₃
    subst hsplit₁ hsplit₂ hsplit₃
    simp_all only
    rfl

/-
theorem concat_correctness (f : ByteArray → ByteArray) (xs ys : ByteArray) 
  (h : ∀ xs ys, f (xs ++ ys) = f xs ++ f ys) 
  : f (xs ++ ys) = concat (f xs) (f ys) :=
  by
    rw [concat]
    rw [h]
-/
