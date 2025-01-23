/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.

Based on `Defining Natural Numbers` in Section 7 of `Theorem Proving in Lean 4`
-/

/-
## Natural Numbers
## Part 4: Inequalities & Division with Remainder
-/


import Library.Theory.S2.P1
import Library.Theory.S2.P2
import Library.Theory.S2.P3

set_option linter.unusedTactic false
set_option pp.fieldNotation false

namespace Math301
namespace Nat

-- Next we use addition in order to define the "less than" relation `lt`. Unlike our other definitions, this one is not defined recursively. We can still think of `lt` as a binary operation which takes in two inputs, but now instead of outputting a natural number, it output a boolean value of `True` or `False`. That's why `lt a b : Prop`, which means that the expression `lt a b` has type `Prop`, which is Lean's way of saying a boolean.
def lt (a b : Nat) : Prop :=
  ∃ (c : Nat), c ≠ zero ∧ a + c = b

-- Another interesting feature of this definition is the use of the existential quantifier. This means that when we want to directly prove a goal of the form `a < b`, we will need to employ the `use` tactic to tell Lean what the `c` value should be such that `a + c = b`.

-- Can you guess what this does?
instance : LT Nat where
  lt := lt

-- To warm-up, give a definition of "less than or equal to" ≤ `le`
def le (a b : Nat) : Prop :=
  sorry

instance : LE Nat where
  le := le

theorem lt_def (a b : Nat) : (∃ (c : Nat), c ≠ zero ∧ a + c = b) → a < b := by
  sorry
  done

theorem le_def (a b : Nat) : a < b ∨ a = b ↔ a ≤ b := by
  sorry
  done

theorem zero_lt_pos (a : Nat) : a ≠ zero → zero < a := by
  sorry
  done


-- The last two theorems should be more of a challenge. I suggest sketching out the proof on paper first before you embark on the formalization.
theorem lt_succ_le (a b : Nat) : a < b → succ a ≤ b := by
  sorry
  done


-- Good luck!
-- Hint: `induction'` on `a`
theorem div_with_rem (a b : Nat) : b ≠ zero → ∃ (q r : Nat), (a = q * b + r ∧ r < b) := by
  sorry
  done

end Nat
end Math301
