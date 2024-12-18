import Mathlib
import Mathlib.Data.List.Sort 
import Lean
open Lean Elab Meta

/- This is the util defined in Atoms.lean -/
def sum : Nat → Nat → Nat := Nat.add

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
    apply Nat.add_eq

theorem wc_correctness' (wc : String → Nat × Nat)
  (h : ∀ xs ys, wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys)) : 
  wc (xs ++ ys) = pairwise_sum (wc xs) (wc ys) :=
  by
    rw [h]

/- Some old work using the actual wc function
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
    apply String.length_append
-/
