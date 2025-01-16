/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/
import Mathlib.Tactic -- imports all the Lean tactics

variable (P Q R S : Prop)

/-!

# Logic in Lean
# Part 6: or ∨

We learn how to manipulate `P ∨ Q` in Lean.

## Tactics

* `left` and `right`
* `cases'` (new functionality)
* `assumption`

-/

-- ## P ∨ Q in a hypothesis
-- When we assume `P ∨ Q` is true, we only know that either `P` or `Q` (or both) are true, but we do not know which one. Thus in order to use `P ∨ Q` as a hypothesis we need to consider cases. The tactic `cases'` also works in this setting. Here is an example:

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq hpr hqr
  cases' hpq with hp hq   -- Split the hypothesis `hpq : P ∨ Q` into two cases; in the first case have `hp : P` and in the second case we have `hq : Q`. The goal will be the same in both.
  · apply hpr hp
  · apply hqr hq
  done

-- ## P ∨ Q in a goal
-- To prove a goal of `P ∨ Q`, we need to prove either `P` or `Q`. We can change our goal to `P` or `Q` using the `left` and `right` tactics, respectively.

example : P → P ∨ Q := by
  intro hp
  left        -- Replaces our goal with `P`
  assumption  -- When the goal exactly matches one of our hypotheses we can be lazy and use the `assumption` tactic instead of using `exact` and saying which of our assumptions it is.
  done

example : Q → P ∨ Q := by
  intro hq
  right
  assumption
  done

-- ## Problems

example : P ∨ Q → (P → R) → (Q → R) → R := by
  sorry
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  sorry
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  sorry
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
