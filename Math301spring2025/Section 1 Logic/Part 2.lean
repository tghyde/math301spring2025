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
# Part 2: True and False

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the problems in this part you will need to know the tactics from Part 1, plus the following two new ones. Check out their explanations here
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/tactics.html
Or just try them out and hover over them to see if you can understand what's going on.

* `trivial` -- Previously called `triv`, recently updated
* `exfalso`

-/

-- ## Worked Examples

-- The terms `True` and `False` are special terms of type `Prop`. If you ever encounter some term and you are not sure what type it is, you can use the `#check` command. Try clicking to the right of the following lines.
#check True
#check False

-- `True` is a proposition which comes with a default proof. This default proof is called `True.intro`. The following line shows us that this really is proof of `True`.
#check True.intro

example : True := by
  exact True.intro
  done

-- Alternatively, when we have truly simple goals there is a tactic called `trivial` which can automatically take care of them for us.
example : True := by
  trivial
  done

-- `False` is a proposition which, so long as mathematics is consistent, has no proof. It should be impossible to construct any term of type `False` unless we have a contradictory hypothesis. Any conclusion follows from a contradictory hypothesis. The `exfalso` tactic replaces any goal with `False`; we only use this when we can deduce a contradiction from our hypotheses. This can be useful when doing a proof by contradiction.

-- Here we show how any proposition follows from `False`.
example : False → P := by
  intro hf -- Assume `False`
  exfalso  -- Change goal to `False`
  exact hf -- We win! You can also use `trivial` here without explicitly mentioning `hf`.
  done

-- ## Problems

example : True → True := by
  sorry
  done

example : False → True := by
  sorry
  done

example : False → False := by
  sorry
  done

example : (True → False) → False := by
  sorry
  done

example : True → False → True → False → True → False := by
  sorry
  done

example : P → (P → False) → False := by
  sorry
  done

example : (P → False) → P → Q := by
  sorry
  done

example : (True → False) → P := by
  sorry
  done
