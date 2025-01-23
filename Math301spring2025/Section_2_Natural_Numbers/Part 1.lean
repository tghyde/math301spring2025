/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.

Based on `Defining Natural Numbers` in Section 7 of `Theorem Proving in Lean 4`
-/

/-
## Natural Numbers
## Part 1: Addition
-/

import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedTactic false
set_option pp.fieldNotation false

namespace Math301 -- Here we create a `namespace` in order to avoid conflicts with the standard math library `Mathlib`. Everything between `namespace Math301` and `end Math301` belongs in the `namespace` called `Math301`. Think of this like a bubble where we can do anything without worrying about contradicting something already done elsewhere. For example, natural numbers are already constructed in `Mathlib` with the same name `Nat`, but we are reconstructing them for ourselves.

/-
`inductive types` allow us to construct mathematical objects recursively. The mathematician `Giuseppe Peano` devised a brilliantly simple way to recursively construct the natural numbers (`Peano's axioms`) as follows: We start with a function called the `successor function` (or `succ` for short) which you can think of as the function `n ↦ n + 1`. We then declare that any natural number `n` is either equal to 0 or is the successor of some other natural number. Thus the natural numbers are `zero`, `succ zero`, `succ succ zero`, etc. In this way the natural numbers are encoded as the number of iterations of `succ` applied to `zero`.
-/
-- This is the syntax for an `inductive type`
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

-- We will put everything we prove about natural numbers inside its own namespace
namespace Nat

/-
What's beautiful about this recursive construction of ℕ, besides its simplicity, is that it allows us to naturally prove everything about natural numbers using induction: To show a fact is true about all natural numbers, it suffices to show it is true for zero (the base case) and that if it is true for `a : Nat`, then it is also true for `succ a`.

We can also recursively define functions on the natural numbers. For example, here is one way to define addition:
-/

def add (a b : Nat) : Nat :=          -- We define addition recursively based on the second parameter `b`
  match b with
  | Nat.zero   => a                   -- If `b = 0`, then we define `add a b := a`
  | Nat.succ c => Nat.succ (add a c)  -- Otherwise, `b = succ c` for some `c : Nat`, and then we define `add a b := succ add a c`.


-- These next two lines allow us to write `a + b` and have Lean interpret that as `add a b`.
instance : Add Nat where
  add := add


-- The following theorems hold by definition.
theorem add_zero (a : Nat) : a + zero = a := by rfl
theorem add_succ (a b : Nat) : a + succ b = succ (a + b) := by rfl
-- We define this as theorems to make it easier to refer to them.

-- On the other hand, if we want to prove that `0 + n = 0`, we need to do an inductive proof.
theorem zero_add (b : Nat) : zero + b = b := by
  induction' b with b ih  -- The tactic `induction'` tells us we are doing an induction, the `'` means it is a more streamlined version of an older tactic just called `induction`. The first `b` says we are doing an inductive argument on that parameter. After the `with` we say what we want to call our variable in the induction and give a name to our inductive hypothesis `ih`.
  · rfl /- Base case -/
    -- Note that 0 + 0 = 0 by definition

  · rw [add_succ, ih] /- Inductive step -/
    -- In this case we are trying to prove an equality, so we can apply a sequence of rewrites to the goal.
    -- Notice that as you move through the steps within the brackets, the goal changes
  done

-- Here is another example
theorem succ_add (a b : Nat) : (succ a) + b = succ (a + b) := by
  induction' b with b ih
  · rfl
  · rw [add_succ, ih, add_succ]
    -- The theorem `add_succ` takes two inputs, but when we use it here we don't have to specify them. Lean is smart enough to figure out what the inputs should be
  done

-- Here we define the `predecessor` function, or `pred`.
-- `pred` should be the inverse of `succ`, at least on all positive natural numbers.
def pred (a : Nat) : Nat :=
  match a with
  | Nat.zero => zero  -- We know that `pred zero` should either be -1 or undefined, but in Lean we have to define the function at all inputs and we are not allowed to give a value not of type `Nat`. Although it seems strange, we can define `pred zero` to be *anything* we want, since we know that it should not be defined there. Here I chose a convenient default value of `zero`. More on this later.
  | Nat.succ b => b

theorem pred_succ (a : Nat) : pred (succ a) = a := by rfl

-- Now it's your turn!
-- Tip: When in doubt, try induction on the second variable.

-- Associativity of addition
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  sorry
  done

-- Commutativity of addition
theorem add_comm (a b : Nat) : a + b = b + a := by
  sorry
  done

-- `succ` is injective
theorem succ_inj (a b : Nat) : succ a = succ b ↔ a = b := by
  sorry
  done

-- `pred` is a right inverse of `succ` on positive integers
theorem succ_pred (a : Nat) : a ≠ zero → succ (pred a) = a := by
  sorry
  done

-- `pred` is injective
theorem pred_inj (a b : Nat) : a ≠ zero → b ≠ zero → (pred a = pred b → a = b) := by
  sorry
  done

-- Addition is right cancellative
theorem add_right_cancel (a b c : Nat) : a + c = b + c → a = b := by
  sorry
  done

-- Addition is left cancellative
-- Note: When you apply a theorem without parameters using the `rw` tactic, it will replace all matching occurrences at the "outer level". Sometimes you don't want this. One way to pin down a specific instance is to say explicitly which inputs it should apply to. You may find this helpful in this proof.
theorem add_left_cancel (a b c : Nat) : c + a = c + b → a = b := by
  sorry
  done

end Nat
end Math301
