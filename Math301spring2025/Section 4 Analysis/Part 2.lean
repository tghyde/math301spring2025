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
  sorry
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
  sorry
  done

-- Now for a challenge. You may need to look up some theorems about inequalities. I used `add_le_add`, `mul_lt_mul`, and a few similar results to do this.

theorem mul_limit
(a b : ℕ → ℝ)
(k l : ℝ)
(hak : tends_to a k)
(hbl : tends_to b l)
: tends_to (a * b) (k * l) := by
  sorry
  done
end Math301
