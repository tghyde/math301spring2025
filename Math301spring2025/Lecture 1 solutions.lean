import Mathlib.Tactic

set_option linter.unusedTactic false
-- First demonstration of Lean

-- Let's prove there are infinitely many primes
theorem infinitely_many_primes : ∀ n : ℕ, ∃ p > n, Nat.Prime p := by
  intro n
  let m := Nat.factorial n + 1
  let q := Nat.minFac m
  use q
  have h₀ : Nat.Prime q := by
    refine Nat.minFac_prime ?_
    linarith [Nat.factorial_pos n]
  constructor
  · by_contra h
    push_neg at h
    have h₁ : q ∣ Nat.factorial n := by
      refine Nat.dvd_factorial ?_ h
      exact Nat.minFac_pos m
    have h₂ : q ∣ m := by
      exact Nat.minFac_dvd m
    have h₃ : q ∣ 1 := by
      exact (Nat.dvd_add_iff_right h₁).mpr h₂
    have h₄ : q = 1 := by
      exact Nat.eq_one_of_dvd_one h₃
    have h₅ : q ≠ 1 := by
      exact Nat.Prime.ne_one h₀
    apply h₅ h₄
    done
  · exact h₀
    done
  done

-- Define a continuous function f : ℝ → ℝ.
def is_continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, (|x - y| < δ → |f x - f y| < ε)

-- Prove that the sum of continuous functions is continuous
theorem sum_of_continuous_is_continuous : ∀ (f : ℝ → ℝ) (g : ℝ → ℝ), is_continuous f →  is_continuous g → is_continuous (f + g) := by
  intro f g hf hg
  rw [is_continuous]
  intro x ε hε 
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf x (ε/2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg x (ε/2) (by linarith)
  use min δ₁ δ₂
  constructor
  · exact lt_min hδ₁ hδ₂
  · intro y hy
    calc
      |(f + g) x - (f + g) y| = |f x + g x - (f y + g y)| := by rfl
      _ = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := by exact abs_add_le (f x - f y) (g x - g y)
      _ < (ε/2) + (ε/2) := by 
        refine add_lt_add ?_ ?_
        · apply h₁
          calc
            |x - y| < min δ₁ δ₂ := by exact hy
            _ ≤ δ₁ := by exact min_le_left δ₁ δ₂
        · apply h₂
          calc
            |x - y| < min δ₁ δ₂ := by exact hy
            _ ≤ δ₂ := by exact min_le_right δ₁ δ₂
        done
      _ = ε := by exact add_halves ε
    done
  done
