/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/

-- imports all of the tactics in Lean's maths library
import Mathlib.Tactic

-- Set's a certain option for convenience
set_option linter.unusedTactic false

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions. `P : Prop` means that `P` is a proposition.
variable (P Q R : Prop)

/-
# Logic in Lean
# Part 1: Implies →

A *proposition* is a true-false statement, like `2+2=4` or `2+2=5` or the Riemann hypothesis. In algebra we manipulate numbers whilst not knowing what the numbers actually are; the trick is that we call the numbers `x` and `y` and so on. In this sheet we will learn how to manipulate propositions without saying what the propositions are -- we'll just call them things like `P` and `Q`.

The purpose of these first few parts is to teach you some basic *tactics*. In particular we will learn how to manipulate statements such as "P implies Q", which is itself a proposition. In Lean we use the notation `P → Q` for "P implies Q". You can get this arrow by typing `\to` or `\r`. Mathematicians usually write the implication arrow as `P ⇒ Q` but Lean prefers a single arrow.
-/

-- ## The absolute basics

/-
An `example` is a theorem that we can prove, but we don't give it a name. In this simple example we are proving that if you assume `P`, `Q`, and `R`, then `P` is true. There are several colons `:` below, the one not in parentheses is separating our hypotheses from the conclusion. When we write `hP : P` means that `hP` is a proof that `P` is true. You can also regard `hP` as the hypothesis that `P` is true; logically these are the same. Note that the `P,Q,R` are the `Prop` variables we defined above, but the `hP, hQ, hR` are new names we made up for proofs of `P,Q,R`.

Try clicking inside this example to the left of the `exact hP`
-/
example (hP : P) (hQ : Q) (hR : R) : P := by

  -- If you look in the `Lean Infoview` panel under `Tactic state` you should see a small block of text that starts with `1 goal`. We are now in the middle of a Lean proof. The statement to the right of `⊢` is your goal, in this case to prove `P`. The stuff above the `⊢` symbol is your assumptions. In this example, we are already assuming `P` is true and `hP` is a proof of `P`. So there's not much to do: we use the `exact` tactic followed by a proof which exactly matches our goal. Try clicking to the right of the `exact hP`.

  exact hP
  -- Since we have achieved our goal, Lean tells us that we have `No goals` at this point, which means we are done. Note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.

  done -- This is the `done` tactic which just helps Lean separate our proofs; it is not strictly necessary.

  -- You may see some things underlined in yellow or faded out. This is Lean telling you that certain things you have written were useless. For example, the hypotheses `hQ` and `hR` did not get used and can be safely removed. Also the `done` tactic can be deleted.

/-
## Tactics you will need

To solve the problems in this part you will need to know how to use the following three tactics:

* `intro`
* `exact`
* `apply`

You can read the descriptions of these tactics in Part C of these notes
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/tactics/tactics.html
In this course we'll be learning about 30 tactics in total; the goal of Section 1 is to get you up to speed with ten basic tactics.

## Worked Examples

Click around in the proofs to see the tactic state in the infoview change. I will use the following conventions: variables with capital letters like `P`, `Q`, `R` denote propositions (i.e. true/false statements) and variables whose names begin with `h` like `h1` or `hP` are proofs or hypotheses.
-/

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Same example as above: assume that `P` and `Q` and `R` are true, but this time give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish
  done

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- In order to prove a statement of the form `P → Q`, we start by assuming `P` is true and then deducing that `Q` must be true. In order to extract that assumption from our goal we use the `intro` tactic. This will add a new hypothesis `hP` to our list of assumptions, it is the hypothesis that `P` is true.
  intro hP
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- Again, note that `exact Q` doesn't work: `exact` takes the *term* `hQ`, not the type `Q`.
-- This example is not very interesting; we assumed `P` but we did not use that assumption. We were also assuming `Q`, and we just used that assumption. However the `intro` step was still important as it helped us get isolate our goal.
  done



-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (hPQ : P → Q) (hP : P) : Q := by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply hPQ -- The `apply` tactic takes a hypothesis of the form `P → Q`. Writing `apply hPQ` changes our goal from `Q` to `P`. Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to prove P.
  exact hP -- Our goal is now `⊢ P`.
  done

-- In Lean, tactics will by default act on the goal. That is, the most natural way to write a proof in Lean is to work backwards; this takes some getting used to.

-- Here is an alternative way to use `apply`
example (hPQ : P → Q) (hP : P) : Q := by
  -- `hP` says that `P` is true, and `hPQ` says that `P` implies `Q`, so `apply hPQ hP` "applies" `P → Q` to `P` to get the conclusion `Q`
  apply hPQ hP -- if we follow `apply hPQ` with `hP` which matches the type of the "input" of `hPQ`, then as a result we get a proof of type `Q`, which finishes our proof.
  done

/-

## Problems

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`.
-/

-- Every proposition implies itself.
example : P → P := by
  sorry
  done

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, `P → (Q → R)` is equivalent to saying that `(P and Q) → R`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and use these to prove `Pn`.

The next problem asks you to prove that `P → (Q → P)`.
-/
example : P → Q → P := by
  sorry
  done

-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. This is called "Modus Ponens" by logicians.
example : P → (P → Q) → Q := by
  sorry
  done

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then so is `P → R`. -/
example : (P → Q) → (Q → R) → P → R := by
  sorry
  done

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get two goals! Note that tactics only operate on the first goal.
example : (P → Q → R) → (P → Q) → P → R := by
  sorry
  done



-- Here are some harder problems. I encourage you to not spend much effort trying to interpret what they mean, but to instead view them as symbolic puzzles. The goal is to get into the rhythm of recognizing the shape of a goal and formally unpacking it.

variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  sorry
  done

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry
  done

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry
  done

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry
  done

example : (((P → Q) → Q) → Q) → P → Q := by
  sorry
  done

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  sorry
  done
