import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/- This is the concatAgg defined in Aggregators/Concat.lean
  def concatAgg (acc x : ByteArray) : ByteArray :=
    acc ++ x
-/

/- `concat` preserves the base case -/
theorem concat_base_case (f: ByteArray → ByteArray) (h : f ByteArray.empty = ByteArray.empty)
  : concatAgg (f ByteArray.empty) (f ByteArray.empty) = ByteArray.empty :=
  by
    rw [concatAgg]
    rw [h]
    rfl

/- `concat` preserves the size of the input -/
lemma concat_size : ∀ xs ys, (concatAgg xs ys).size = xs.size + ys.size :=
  by
    intro xs ys
    rw [concatAgg]
    simp [ByteArray.size_append]

/- The length of the output after f is less than or equal to the length of the output after ++ -/
theorem concat_ordering_lt (f : ByteArray → ByteArray → ByteArray)
  (h : ∀ xs ys, (f xs ys).size <= (xs ++ ys).size) :
  ∀ xs ys a b c d,
    xs = a ++ b →
    ys = c ++ d →
    (concatAgg (f a c) (f b d)).size <= (xs ++ ys).size :=
  by
    intro xs ys a b c d hsplit hsplit1
    rw [concatAgg, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

/- The length of the output after f is greater than or equal to the length of the output after ++ -/
theorem concat_ordering_gt (f : ByteArray → ByteArray → ByteArray)
  (h : ∀ xs ys, (f xs ys).size >= (xs ++ ys).size) :
  ∀ xs ys a b c d,
    xs = a ++ b →
    ys = c ++ d →
    (concatAgg (f a c) (f b d)).size >= (xs ++ ys).size :=
  by
    intro xs ys a b c d hsplit hsplit1
    rw [concatAgg, hsplit, hsplit1]
    have h₁ := h a c
    have h₂ := h b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

/-- The output of concatAgg is smaller than its input -/
theorem concat_size_lt (f: ByteArray → ByteArray)
  (h: ∀ input, (f input).size <= input.size) :
    ∀ str a b, str = a ++ b → (concatAgg (f a) (f b)).size <= str.size :=
  by
    intro s a b hsplit
    rw [concatAgg]
    rw [hsplit]
    have h₁ := h a
    have h₂ := h b
    simp [ByteArray.size_append]
    exact Nat.add_le_add h₁ h₂

/-- This concatAgg uses List String instead of ByteArray.
    This is necessary because ByteArray does not have membership. -/
def concat_list (acc x : List String) : List String :=
  acc ++ x

/-- concatAgg preserves membership -/
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
    concatAgg (f xs) (f ys) = concatAgg (f a) (f b) ++ concatAgg (f c) (f d) :=
  by
    intro input xs ys a b c d hsplit₁ hsplit₂ hsplit₃
    subst hsplit₁ hsplit₂ hsplit₃
    simp_all only
    rfl

/- Doesn't hold if f is a constant function that returns "a" -/
theorem concat_equality (f : ByteArray → ByteArray) (xs ys : ByteArray) (h: f xs = f ys) :
  ∀ a b c d, xs = a ++ b → ys = c ++ d → concatAgg (f a) (f b) = concatAgg (f c) (f x) := sorry

lemma concat_idempotence (f : ByteArray → ByteArray) :
  ∀ a b c d, concatAgg (f a) (f b) = c ++ d → concatAgg (f a) (f b) = concatAgg c d :=
  by
    intro a b c d hsplit
    simp_all only
    rfl

/-
theorem concat_correctness (f : ByteArray → ByteArray) (xs ys : ByteArray)
  (h : ∀ xs ys, f (xs ++ ys) = f xs ++ f ys)
  : f (xs ++ ys) = concatAgg (f xs) (f ys) :=
  by
    rw [concatAgg]
    rw [h]
-/
