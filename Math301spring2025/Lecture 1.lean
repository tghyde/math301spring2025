import Mathlib.Tactic

-- First demonstration of Lean

-- Let's prove there are infinitely many primes
theorem infinitely_many_primes : ∀ n : ℕ, ∃ p > n, Nat.Prime p := by
  sorry
  done

-- Define a continuous function f : ℝ → ℝ.
def is_continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, (|x - y| < δ → |f x - f y| < ε)

-- Prove that the sum of continuous functions is continuous
theorem sum_of_continuous_is_continuous : ∀ (f : ℝ → ℝ) (g : ℝ → ℝ), is_continuous f →  is_continuous g → is_continuous (f + g) := by
  sorry
  done
