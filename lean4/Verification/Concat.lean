import Synthesis.Atoms
import Mathlib
import Mathlib.Data.List.Sort
import Lean
open Lean Elab Meta

/- This is the concatAgg defined in Aggregators/Concat.lean
  def concatAgg (acc x : ByteArray) : ByteArray :=
    acc ++ x
-/

/- `concatAgg` preserves the base case -/
lemma concat_base_case : 
  concatAgg ByteArray.empty ByteArray.empty = ByteArray.empty := by
  rfl

/- `concatAgg` preserves the size of the input -/
lemma concat_size : ∀ xs ys, (concatAgg xs ys).size = xs.size + ys.size :=
  by
    intro xs ys
    rw [concatAgg]
    simp [ByteArray.size_append]

/-- This concatAgg uses List String instead of ByteArray.
    This is necessary because ByteArray does not have membership. -/
def concatList (acc x : List String) : List String :=
  acc ++ x

/-- `concatList` preserves membership -/
lemma concat_membership (f: List String → List String)
  (h : ∀ lines, ∀ line ∈ (f lines), line ∈ lines) :
  ∀ lines a b, lines = a ++ b → ∀ line ∈ (concatList (f a) (f b)),  line ∈ lines :=
  by
    intro lines a b hsplit line
    rw [concatList]
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

-- Examples
namespace ConcatExample

-- `foo` is a black-box implementation of `cat`
-- It takes a single argument and returns the same value
opaque foo : ByteArray → ByteArray
axiom foo_base_case : foo ByteArray.empty = ByteArray.empty
axiom foo_size : ∀ input, (foo input).size = input.size
axiom foo_append : ∀ a b, foo (a ++ b) = foo a ++ foo b

opaque xs : ByteArray
opaque ys : ByteArray
axiom foo_equality : foo xs = foo ys

theorem parallel_foo_base_case : 
  concatAgg (foo ByteArray.empty) (foo ByteArray.empty) = ByteArray.empty :=
  by
    rw [foo_base_case, concat_base_case]

theorem parallel_foo_size :
    ∀ str a b, str = a ++ b → (concatAgg (foo a) (foo b)).size = str.size :=
  by
    intro s a b hsplit
    rw [concat_size]
    rw [hsplit]
    have h₁ := foo_size a
    have h₂ := foo_size b
    simp [ByteArray.size_append]
    linarith

theorem parallel_foo_append :
  ∀ input xs ys a b c d,
    input = xs ++ ys →
    xs = a ++ b →
    ys = c ++ d →
    concatAgg (foo xs) (foo ys) = concatAgg (foo a) (foo b) ++ concatAgg (foo c) (foo d) :=
  by
    intro input xs ys a b c d hsplit₁ hsplit₂ hsplit₃
    simp [hsplit₁, hsplit₂, hsplit₃, foo_append, concatAgg]

theorem parallel_foo_equality : ∀ a b c d, xs = a ++ b → ys = c ++ d → 
  concatAgg (foo a) (foo b) = concatAgg (foo c) (foo d) := 
  by
    intro a b c d hsplit₁ hsplit₂
    simp only [concatAgg, ByteArray.append_eq]
    rw [←foo_append a b, ←foo_append c d, ←hsplit₁, ←hsplit₂]
    exact foo_equality

theorem parallel_foo_idempotence : ∀ a b c d, concatAgg (foo a) (foo b) = c ++ d 
  → concatAgg (foo a) (foo b) = concatAgg c d :=
  by
    intro a b c d hsplit
    simp_all only
    rfl

-- `bar` is a black-box implementation of `grep`
-- Unlike `foo`, `bar` takes two arguments 
-- And the size of the output is less than or equal to the size of the input
opaque bar : ByteArray → ByteArray → ByteArray
axiom bar_size : ∀ xs ys, (bar xs ys).size <= (xs ++ ys).size

theorem parallel_bar_size :
  ∀ xs ys a b c d,
    xs = a ++ b →
    ys = c ++ d →
    (concatAgg (bar a c) (bar b d)).size <= (xs ++ ys).size :=
  by
    intro xs ys a b c d hsplit hsplit1
    rw [concat_size, hsplit, hsplit1]
    have h₁ := bar_size a c
    have h₂ := bar_size b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

-- `baz` is some function that takes two arguments 
-- and returns more than the sum of the sizes of the inputs
opaque baz : ByteArray → ByteArray → ByteArray
axiom baz_size : ∀ xs ys, (baz xs ys).size >= (xs ++ ys).size

theorem parallel_baz_size :
  ∀ xs ys a b c d,
    xs = a ++ b →
    ys = c ++ d →
    (concatAgg (baz a c) (baz b d)).size >= (xs ++ ys).size :=
  by
    intro xs ys a b c d hsplit hsplit1
    rw [concatAgg, hsplit, hsplit1]
    have h₁ := baz_size a c
    have h₂ := baz_size b d
    simp [ByteArray.size_append]
    simp [ByteArray.size_append] at h₁
    simp [ByteArray.size_append] at h₂
    linarith

end ConcatExample
