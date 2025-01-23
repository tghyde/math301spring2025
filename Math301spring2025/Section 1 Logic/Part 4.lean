/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.unusedTactic false

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

/-!

# Logic in Lean
# Part 4: and ∧

We learn how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'` -- Note the apostrophe '
* `constructor`

The expression `P ∧ Q` is a proposition which means `P and Q`. The way we handle terms of type `P ∧ Q` depends on whether they show up in our hypotheses or in our goal.

## P ∧ Q in a hypothesis
If we have an assumption `hpq : P ∧ Q`, then this means `hpq` is a proof of both `P` and `Q`. From this we can extract proofs of `P` and `Q` individually like this: `hpq.1 : P` and `hpq.2 : Q`. Alternatively you can write `hpq.left : P` and `hpq.right : Q`.
-/

example : P ∧ Q → P := by
  intro hpq
  exact hpq.1 -- Extract a proof of the left part of the `and`
  done

-- Note that `∧` is always interpreted as a binary operation. If you write an expression like `P ∧ Q ∧ R`, this really means `P ∧ (Q ∧ R)`. Hence if `hpqr : P ∧ Q ∧ R`, then `hpqr.1 : P` and `hpqr.2 : Q ∧ R`.

/-
## P ∧ Q in a goal
If we have a goal that includes a proposition of the form `P ∧ Q`, that means we need to construct a proof of both `P` and `Q`. The tactic `constructor` splits a goal into two parts, the first with a goal of `P` and the second with a goal of `Q`.
-/

example : P → (P → Q) → P ∧ Q := by
  intro hp hpq -- We can use one intro to iteratively pull off the arrows from our goal.
  constructor -- Our goal is of the form `P ∧ Q`, so we use `constructor` to split it.
  · exact hp -- Our first goal is `P`, which is a hypothesis
  · apply hpq hp -- Our second goal is `Q`, which quickly follows from our hypotheses
  done

-- Alternatively, instead of using `constructor` we can manually construct terms of type `P ∧ Q` using ordered pairs: If `hp : P` and `hq : Q`, then `⟨hp, hq⟩ : P ∧ Q`. Use `\<` and `\>` to get the angle brackets for the ordered pair. This is useful when the proofs of each part are very simple. Here is the above example done with this method.
example : P → (P → Q) → P ∧ Q := by
  intro hp hpq
  exact ⟨hp, by apply hpq hp⟩ -- The keyword `by` tells Lean we are starting a `tactic proof`
  done

-- `Tactics` are "metaprograms" which automatically fill in a bunch of Lean details for us. For complex proofs, they can save us a lot of effort and make our proofs more readable. But for simpler proofs it can be more straightforward to skip the tactics. Here is the above example one more time, but skipping the tactic proof inside the brackets:

example : P → (P → Q) → P ∧ Q := by
  intro hp hpq
  exact ⟨hp, hpq hp⟩ -- Writing the term `hpq : P → Q` followed by the term `hp : P` automatically gives us a term `hpq hp : Q`.
  done

-- Which way you choose to do it is a matter of personal style (IMO).

-- ## Problems

example : P ∧ Q → Q := by
  sorry
  done

example : (P → Q → R) → P ∧ Q → R := by
  sorry
  done

example : P → Q → P ∧ Q := by
  sorry
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  sorry
  done

example : P → P ∧ True := by
  sorry
  done

example : False → P ∧ False := by
  sorry
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry
  done

example : (P ∧ Q → R) → P → Q → R := by
  sorry
  done
