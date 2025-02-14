/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
## Analysis
## Part 2: Sequences and Limits
-/

namespace Math301

-- In this part we begin studying sequences of real numbers and their limits. A convenient way to encode a sequence `a_n` of real numbers in Lean is as a function `a : ℕ → ℝ` which sends `n : ℕ` to the nth term `a n`. Below we define what it means for a sequence to converge to a limit.

def tends_to (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - l| < ε

-- Here is an example of how we can work with limits using the tactics we learned from `Part 1`.
theorem add_limit
  (a b : ℕ → ℝ)
  (k l : ℝ)
  (hak : tends_to a k)
  (hbl : tends_to b l)
  : tends_to (a + b) (k + l) := by
    intro ε hε
    -- It helps to work this out on paper ahead of time so you know what you plan to do. In this case we're going to use an `ε/2` trick. First we extract integers `M` and `N` from our hypotheses. The `(by linarith)` parts are justifying that `ε/2 > 0` which we need to get past the first two parts in the definition of `tends_to`.
    have ⟨M,hM⟩ := hak (ε/2) (by linarith)
    have ⟨N,hN⟩ := hbl (ε/2) (by linarith)
    use max M N

    -- Proving these as subgoals here will help us automate part of our argument later
    have h₁ : M ⊔ N ≥ M := Nat.le_max_left M N
    have h₂ : M ⊔ N ≥ N := Nat.le_max_right M N

    intro n hn
    calc
      |(a + b) n - (k + l)|
        = |(a n - k) + (b n - l)| := by simp; ring
      _ ≤ |a n - k| + |b n - l|   := abs_add_le _ _
      _ < (ε/2) + (ε/2)           := by
      -- Since the proof of this step is longer, we put it in curly braces to help visually set it apart.
        {
          apply add_lt_add
          · apply hM
            trans (M ⊔ N) <;> assumption
          · apply hN
            trans (M ⊔ N) <;> assumption
        }
      _ = ε                       := by ring
    done


-- Now it is your turn!

-- You may need to use the theorem `add_lt_add_of_le_of_lt`.
theorem converges_bdd
(a : ℕ → ℝ)
(l : ℝ)
(hal : tends_to a l)
: ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| < ε + |l| := by
  intro ε hε
  specialize hal ε hε
  have ⟨N,hN⟩ := hal
  use N
  intro n hn
  calc
    |a n| = |(a n - l) + l| := by ring
        _ ≤ |a n - l| + |l| := abs_add_le _ _
        _ < ε + |l|         := by {
          rw [add_comm, add_comm ε]
          apply add_lt_add_of_le_of_lt
          · linarith
          · apply hN n hn
          }
  done

-- Define constant sequences. The `@[simp]` makes it so that the `simp` tactic will use this definition when trying to simplify expressions.
@[simp]
def const (c : ℝ) : ℕ → ℝ := fun n => c

-- You may need the theorems `abs_nonneg` and `abs_mul`
theorem scalar_limit
(a : ℕ → ℝ)
(c l : ℝ)
(hal : tends_to a l)
: tends_to ((const c) * a) (c*l) := by
  intro ε hε
  simp
  by_cases hc : c = 0
  · use 0
    intro n hn
    rw [hc]
    ring
    simp
    linarith
    done
  have ⟨N,hN⟩ := hal (ε/|c|) (by field_simp; assumption)
  use N
  intro n hn
  calc
    |c * a n - c * l| = |c * (a n - l)| := by ring
                    _ = |c| * |a n - l| := by rw [abs_mul]
                    _ < |c| * (ε/|c|)   := by {
                      apply mul_lt_mul'
                      · linarith
                      · exact hN n hn
                      · linarith [abs_nonneg (a n - l)]
                      · field_simp; assumption
                      }
                    _ = ε := by field_simp
  done

-- Now for a challenge. You may need to look up some theorems about inequalities. I used `add_le_add`, `mul_lt_mul`, and a few similar results to do this.

theorem mul_limit
(a b : ℕ → ℝ)
(k l : ℝ)
(hak : tends_to a k)
(hbl : tends_to b l)
: tends_to (a * b) (k * l) := by
  intro ε hε
  have ⟨N₁, hN₁⟩ := converges_bdd a k hak 1 (by norm_num)
  have : |k| ≥ 0 := abs_nonneg k
  have : |k| + 1 > 0 := by linarith

  -- First deal with the case when `l = 0`
  by_cases hl : l = 0
  · have ⟨N₂, hN₂⟩ := hbl (ε/(|k| + 1)) (by field_simp; linarith)
    use max N₁ N₂
    intro n hn
    specialize hN₁ n (by linarith [Nat.le_max_left N₁ N₂])
    simp
    calc
      |a n * b n - k * l|
        = |a n * (b n - 0)| := by rw [hl]; ring
      _ = |a n| * |b n - 0| := abs_mul _ _
      _ ≤ (|k| + 1) * |b n - 0| := by {
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          <;> linarith [abs_nonneg (a n), abs_nonneg (b n - 0)]}
      _ < (|k| + 1)*(ε/(|k| + 1)) := by {
          specialize hN₂ n (by linarith [Nat.le_max_right N₁ N₂])
          refine Iff.mpr (mul_lt_mul_left this) ?_
          rw [← hl]
          linarith
          }
      _ = ε := by field_simp
    done

  -- Now suppose that `l ≠ 0`
  have ⟨N₂, hN₂⟩ := hak (ε/(2*|l|)) (by field_simp; assumption)
  have ⟨N₃, hN₃⟩ := hbl (ε/(2*(|k|+1))) (by field_simp; assumption)
  use max N₁ (max N₂ N₃)
  intro n hn

  -- These will be annoying to prove later
  have hn₁ : n ≥ N₁ := by linarith [Nat.le_max_left N₁ (max N₂ N₃)]
  have hn₂ : n ≥ N₂ := by linarith [Nat.le_max_right N₁ (max N₂ N₃), Nat.le_max_left N₂ N₃]
  have hn₃ : n ≥ N₃ := by linarith [Nat.le_max_right N₁ (max N₂ N₃), Nat.le_max_right N₂ N₃]

  simp
  calc
    |a n * b n - k * l|
        = |a n * (b n -  l) + (a n - k) * l| := by ring
      _ ≤ |a n * (b n - l)| + |(a n - k) * l| := abs_add_le _ _
      _ = |a n| * |b n - l| + |a n - k| * |l| := by rw [abs_mul, abs_mul]
      _ ≤ (|k| + 1) * |b n - l| + |a n - k| * |l| := by {
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_right ?_ ?_
          specialize hN₁ n (by linarith)
          · linarith
          · linarith [abs_nonneg (b n - l)]
          done
        · linarith
        }
      _ < (|k| + 1)* (ε/(2*(|k| + 1))) + (ε/(2*|l|))*|l| := by {
        specialize hN₂ n (by linarith)
        specialize hN₃ n (by linarith)
        have : |l| > 0 := by exact Iff.mpr abs_pos hl
        refine add_lt_add ?_ ?_
        · apply mul_lt_mul'
          · linarith
          · assumption
          · linarith [abs_nonneg (b n - l)]
          · assumption
          done
        · apply mul_lt_mul
          · assumption
          · linarith
          · linarith
          · apply div_nonneg
            <;> linarith
            done
          done
        }
      _ = ε := by field_simp; ring
  done
end Math301
