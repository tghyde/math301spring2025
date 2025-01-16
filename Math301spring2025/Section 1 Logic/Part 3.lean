/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/

import Mathlib.Tactic -- import all the tactics

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

/-!

# Logic in Lean
# Part 3: Not ¬

We learn how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → False` are *definitionally equal*. Check out the explanation of definitional equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

We will learn the following tactic in this part:

* `by_cases`

-/

-- ## Worked Examples


example : ¬True → False := by
  intro hT -- Our goal is an implication, so we start with `intro`
  apply hT -- Remember: `¬ True` is by definition equal to `True → False`, so `apply hT` changes our goal to `True`
  trivial
  done

-- The `by_cases` tactic streamlines the use of the law of excluded middle, which tells us that for any proposition `P` the proposition `P or ¬ P` is always true. As input we give `by_cases` a proposition `P` and the name of a proof `hP`. This splits our goal into two parts each with an extra assumption called `hP` in each. In the first part, `hP` is a proof of `P`, and in the second part `hP` is a proof of `¬ P`. We then have to reach our goal in either case.
example : ¬¬P → P := by
  intro hnnp -- Extract our hypothesis
  by_cases hp : P -- Split into cases based on whether `P` is true or false
  -- Use `\.` to get the bullet points which separate the cases
  · trivial -- In this case, we assume `P`, so there is no work to be done.
  · exfalso -- In this case we are assuming both `¬ P` and `¬¬ P`, which gives a contradiction, so we start by replacing our goal with `False`
    apply hnnp hp
  done

-- ## Problems

example : False → ¬True := by
  sorry
  done

example : ¬False → True := by
  sorry
  done

example : True → ¬False := by
  sorry
  done

example : False → ¬P := by
  sorry
  done

example : P → ¬P → False := by
  sorry
  done

example : P → ¬¬P := by
  sorry
  done

example : (P → Q) → ¬Q → ¬P := by
  sorry
  done

example : ¬¬False → False := by
  sorry
  done

example : (¬Q → ¬P) → P → Q := by
  sorry
  done
