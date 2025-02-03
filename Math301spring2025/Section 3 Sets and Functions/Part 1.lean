/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

/-
## Sets and Functions
## Part 1: Set Basics
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
# New tactics

`rintro`
-/

/-
A `set` is mathematical name for a collection of things. Trying to pin down the idea more precisely gets tricky since the notion of a set is so close to the foundations of math. Practically speaking, a `set` is an unordered list of objects which does not have any repeats. If `A` is a set, then every thing `a` either belongs to `A`, in which case we write `a ∈ A`, or it does not `a ∉ A`.

In Lean, every set must have a specified underlying type. For example, `A : Set ℤ` means that `A` is a set of integers. You can make sets out of any type.
-/

-- To start, we declare a few variables we'll use throughout this sheet.
variable (X : Type) (A B C : Set X)

-- Let's prove the following fact.
example : ∀ (x : X), x ∈ A → x ∈ A ∪ B := by
  -- Notice that the goal looks a bit different in the infoview than it does stated above. Lean is automatically abbreviating some things for us.

  -- Our goal begins with `∀ x ∈ A`. If you've taken real analysis, then you know that to start a form with this form we first say `Let x be an element of A`. This is similar to how if we want to prove a statement of the form `P → Q` we begin by saying `Suppose P`. In fact, we can use the same tactice, `intro` to handle both cases.
  intro x

  -- Now our goal looks more like what is stated above. We know what the next step is.
  intro hx

  -- The new goal is `a ∈ A ∪ B`. The set `A ∪ B` is defined by `A ∪ B = {x : X | x ∈ A ∨ x ∈ B}`. To prove that `x ∈ A ∪ B`, our goal is really to prove `x ∈ A ∨ x ∈ B`. Hence to make progress on this goal we can use the `left` or `right` tactics to specify our goal. In this case, `left` will do.
  left

  -- Now the goal has simplified to one of our assumptions.
  assumption
  done

/-
If `A` and `B` are sets, recall that `A ⊆ B` means that every element of `A` also belongs to `B`. We can write this more formally as `∀ (x : X), x ∈ A → x ∈ B`. Thus the following is equivalent by definition to what we did above.
-/

example : A ⊆ A ∪ B := by
  -- Even though you can't see the `∀` in the goal, it is there. The exact same proof will work
  intro x hx
  left
  assumption
  done

-- Many basic set identities are really just disguised logical tautologies. As we saw in Section 1, these could all be knocked out with the `tauto` tactic. Same works here.
example : A ⊆ A ∪ B := by
  tauto
  done

-- ...but for the sake of practice, I encourage you to not use `tauto` just yet. Earn `tauto` now, and we'll use `tauto` later.

/-
Sets are completely determined by their elements, which is to say that two sets `A` and `B` are equal if and only if they have exactly the same elements. This is called the `property of extensionality`. Thus, when we want to prove that two sets are equal `A = B`, the general way to go about this is to show that `A ⊆ B` and `B ⊆ A`. This is such a common task that there's a tactic called `ext` which sets us up for it
-/

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  -- Check out how this changes our goal
  ext x

  -- We can now use `constructor` to break the goal into two parts.
  constructor
  -- When we introduce a compound hypothesis, we can use `rintro` to recursively break down and name each piece of the hypothesis. This saves us several lines of code.
  · rintro ⟨hA,(hB | hC)⟩
    · left
      exact ⟨hA,hB⟩
      done
    · right; exact ⟨hA,hC⟩
      done
    done
  · rintro (⟨hA,hB⟩ | ⟨hA,hC⟩)
    · constructor
      · assumption
      · left; assumption
    -- When we use `exact`, Lean expects us to exactly give terms of the expected types. If we want to use a short tactic argument to contstruct the term, we can use the `by` keyword to enter into tactic mode. You can use a semicolon `;` to puncutate between assertions. It behaves just like moving to a new line.
    · exact ⟨hA, by right; assumption⟩
      done
    done
  done

-- Try these
example : B ∩ C ⊆ (A ∪ B) ∩ (A ∪ C) := by
  sorry
  done

example : (A ∪ B) ∩ A = A := by
  sorry
  done

-- Recall that the `difference` between two sets `B \ A` is defined to be
-- `B \ A = {x ∈ B | x ∉ A}`
-- If you have an assumption `x ∈ B \ A`, this is definitionally equal to `x ∈ B ∧ x ∉ A`.
-- Note that `x ∉ A` is defined to mean `¬(x ∈ A)`.

-- You may need to use `by_cases` for part of this one
example : (A ∩ B) ∪ (B \ A) = B := by
  sorry
  done

-- `Challenge:` see if you can do this in two lines (using ; to combine lines doesn't count).
example : A ∩ (B \ C) ⊆ (A ∩ B) \ C := by
  sorry
  done

example : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  sorry
  done

-- You might find the tactics `push_neg` and `specialize` helpful for this problem.
-- Instead of me explaining it, try reading the documentation to see how they work. Here are links:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/PushNeg.html#Mathlib.Tactic.PushNeg.tacticPush_neg_
-- https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.specialize


example : (∃ x, x ∈ B \ A) ↔ ¬ (B ⊆ A) := by
  sorry
  done
