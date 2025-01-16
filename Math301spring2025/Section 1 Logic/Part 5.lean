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
# Part 5: iff ↔

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

We will learn the following new tactics:

* `rfl`
* `rw`

The tactic `rfl`, short for `reflexive`, proves goals of the form `A = B` or `A ↔ B` where `A` and `B` are `definitionally equal`. There are three levels of equality in Lean:
* `syntactic equality`
* `definitional equality`
* `propositional equality`

Here is a summary of the differences:
“`Syntactic equality` is they look identical, `definitional equality` is they are the same, `propositional equality` is they turn out to be the same.” – Bhavik Mehta

`Syntactic equality` is the easiest for the computer to check, since it just requires checking symbol by symbol that two expressions are the same. `Definitional equality` is when two things are the same by definition, but possibly look different. For example, `¬ P` and `P → False` are definitionally equal but not syntactically equal. You can think of `propositional equality` as equalities we get by proving a theorem. For example `the sum of integers from 1 to n = n(n+1)/2` is a propositional equality since we can prove this is true, but it is not true by definition.

Checking if two expressions are definitionally equal seems easy, but it can actually be quite hard. From Kevin Buzzard's notes:
# Checking definitional equality can be extremely difficult. In fact it is a theorem of logic that checking definitional equality in Lean is undecidable in general. Of course this doesn’t necessarily mean that it’s hard in practice; in the examples we will see in this course rfl should work fine when it is supposed to work. There is a pathological example in Lean’s reference manual of three terms A, B and C where ⊢ A = B and ⊢ B = C can both be proved by rfl, but rfl fails to prove ⊢ A = C (even though they are definitionally equal). Such pathological examples do not show up in practice when doing the kind of mathematics that we’re doing in this course though.
-/

example : (¬ P) ↔ (P → False) := by
  rfl -- Since these two propositions are definitionally equal, `rfl` gets the job done
  done

example : (P ∧ Q) ↔ (Q ∧ P) := by
  rfl -- In this case `rfl` fails because `P ∧ Q` and `Q ∧ P` are propositionally equal but not definitionally equal.
  -- (comment out this example if you want your file to compile with no errors; on Mac, highlight all the text and type `cmd + /` to comment a block of text.)
  done


-- ## P ↔ Q as a hypothesis
-- The proposition `P ↔ Q` behaves as if it were `(P → Q) ∧ (Q → P)`, however they are not definitionally equal (they are propositionally equal). If `hpq : P ↔ Q`, then `h.1 : P → Q` and `h.2 : Q → P`. This allows us to extract each of the component implications.

example : (P ↔ Q) → (P → (R → Q)) := by
  intro hpq hp hr -- Extract all the →
  apply hpq.1 hp  -- Now our goal is `Q` which we can reach by applying `P → Q` to `P`
  done

-- Another way to use a `P ↔ Q` hypothesis is by "rewriting" using the `rw` tactic. If `hpq : P ↔ Q`, then `rw [hpq]` will replace every instance of `P` (up to syntactic equality) in the goal with a `Q`. If you want to do the substitution in the other direction we write `rw [← hpq]` to replace all instances of `Q` with `P` in the goal.

example : (P ↔ Q) → (P → (R → Q)) := by
  intro hpq hp hr -- Extract all the →
  rw [← hpq]      -- Use rw to replace `Q` by `P` in the goal...
  exact hp        -- ...and we're done!
  done

example : (¬ P ↔ Q) → (Q → (P → False)) := by
  intro hnpq hq
  rw [hnpq] -- This `rw` gives an error because it only works up to `syntactic equality`, not `definitional equality`.
  done

-- ## P ↔ Q in a goal
-- We can use the `constructor` tactic to break a goal of type `P ↔ Q` into two goals, the first of tyep `P → Q` and the second of type `Q → P`.

example : (P → Q) → (¬ P → ¬ Q) → (P ↔ Q) := by
  intro hpq hnpnq       -- Extract hypotheses
  constructor           -- Split goal into two parts
  · exact hpq           -- First part is one of our assumptions
  · intro hq            -- The second part is the contrapositive of our other hypothesis. Since `Q → P` is only propositionally equal to `¬ P → ¬ Q`, we need to give a proof.
    by_cases hp : P     -- Let's split by cases depending on whether P is true or false.
    · exact hp          -- If P, then we are done.
    · exfalso           -- Otherwise, if ¬ P, then we have a contradiction with `¬ P`, `Q`, and `¬ P → ¬ Q`, so let's change our goal to `False`.
      apply hnpnq hp hq -- Applying in the correct order we reach our contradiction.
  done

-- You can also use the angle brackets to directly construct a term of type `P ↔ Q` just like we did for `P ∧ Q`.
example : (P → Q) → (Q → P) → (P ↔ Q) := by
  intro hpq hqp
  exact ⟨hpq, hqp⟩ -- Note the order, we have to do `P → Q` in the first component and `Q → P` in the second.
  done

-- ## Problems

example : P ↔ P := by
  sorry
  done

example : (P ↔ Q) → (Q ↔ P) := by
  sorry
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  sorry
  done

example : (P ∧ Q) ↔ (Q ∧ P) := by
  sorry
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry
  done

example : P ∧ Q ↔ Q ∧ P := by
  sorry
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

example : P ↔ P ∧ True := by
  sorry
  done

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  sorry
  done
