/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
## Analysis
## Part 1: Numbers, Algebra, and Inequalities
-/


-- # Coercion
-- Lean has many kinds of numbers implemented. We can refer to these numbers using the same symbols we use in a math class. Try hovering your mouse over each symbol to see info on how these numbers are defined and how to type the symbols.

#check ℕ
#check ℤ
#check ℚ
#check ℝ
#check ℂ

-- What is the type of the number `3`? To find out, we use the `#check` command. Move your cursor to this line, then you'll see `3 : ℕ` in the infoview.
#check 3

-- For basic numerical experssions, Lean will guess that they are the simplest type of number which makes sense. Consider these examples:

#check -3
#check √3

-- Here are a couple that perhaps defy your expectations:

#check 0.75
#check 3/4


-- Both of these look like they should be rational numbers, but the first one says that `0.75` is a float and the second one says that `3/4` is a natural number. What's going on here?

-- `Float` is short for "floating point numbers", which are number with a decimal point and a certain prescribed number of digits. This is a common type in programming languages. If we want Lean to treat `0.75` as a rational number, then we can tell it explicitly like this:

#check (0.75 : ℚ)

-- Lean automatically knows how to do these type conversions, which in computer science are called `coercions`. If you try to coerce something and Lean doesn't know how, it will tell you.

#check (0.75 : ℕ) -- Comment out this line to remove the error from your file

-- The issue with `3/4` is a bit more subtle. To get a clue, we can ask Lean to evaluate this expression.

#eval 3/4

-- Lean thinks `3/4` is `0`, which explains why it thinks this is a natural number. In Lean, every function must be defined on all inputs. We would like to be able to define division of natural numbers so that an expression like `10/2` evaluates to `5`, which it does:

#eval 10/2

-- But if write a division of natural numbers that does not give us a natural number, what should we do? In this case, Lean gives an alternative useful definition. More generally if `m` and `n` are natural numbers, then `m/n` denotes the floor of `m` divided by `n`. This always produces a natural number, and it agrees with division when `n` happens to divide `m`.

#eval 10/3

-- If we want Lean to correctly interpret our fraction, we can explicitly coerce it:

#check (3/4 : ℚ)
#eval (3/4 : ℚ)


-- Commands starting with `#` like `#check`, `#eval`, `#reduce`, and `#print` are diagnostic tools. They do not affect how the Lean code runs/compiles, but rather they provide you helpful messages in the Lean infoview.

-- # Goals with Numbers
-- If you encounter a goal which involves a numerical expression these can almost always be closed using the `norm_num` tactic.

example : 3 + 4 = 7 := by norm_num
example : (3/4 : ℚ) < (4/3 : ℚ) := by norm_num
example : √3^2 = 3 := by norm_num

-- `norm_num` works by reducing numerical expressions to a "normal form" where they can be compared directly. Here, you try:

example : ∃ x : ℝ, 2 + x = 5 := by
  sorry
  done

-- `norm_num` can even close compound goals like `P ∧ Q ∧ R` if they are all numerical
example : ∃ (x y₁ y₂: ℝ), y₁ ≠ y₂ ∧ x^2 + y₁^2 = 1 ∧ x^2 + y₂^2 = 1 := by
  sorry
  done

example : ∃ x, (3*x = 0) → (4*x = 0) := by
  sorry
  done

-- # Goals with algebra
-- If you're trying to prove a goal that follows by basic algebra but includes variables instead of numbers, then `norm_num` won't work. However, there are other tactics we can use. For example, if our goal is simple algebra involving only the ring operations (addition, subtraction, and multiplication (but no division!)), then we can use the `ring` tactic.

example : ∀ (x y : ℝ), (x + y)^2 = x^2 + 2*x*y + y^2 := by
  intro x y
  ring
  done

-- Give it a shot:
example : ∀ x : ℤ, ∃ y z, x + y = z^2 := by
  sorry
  done

-- This also works with variables in the exponents
example : ∀ (x y : ℝ), ∀ n : ℕ, (x^(n+1) + y^(n+1))*(x + y) = x^(n+2) + y^(n+2) + x*y*(x^n + y^n) := by
  sorry
  done

-- If your goal involves division, `ring` won't help you directly. Instead we can first use the `field_simp` tactic which clears denominators, reducing to a goal that ring could potentially handle.
example : ∀ (x : ℝ), (x ≠ 0) →  ∃ y, 1 = x*y := by
  sorry
  done

example : ∀ x y : ℝ, y≠ 0 → (x + y)/y = 1 + x/y := by
  sorry
  done

-- # Goals with general inequalities
-- If you're trying to prove some goal involving variables and inequalities, then `norm_num`, `ring`, and `field_simp` won't work. In this case there is a tactic called `linarith` which has an algorithm for closing such goals using proof by contradiction.
example : ∀ x : ℝ, ∃ y, x < y := by
  intro x
  use x + 1
  linarith
  done

-- If you need to introduce a bunch of variable and hypotheses, but you don't actually need to refer to them yourself, you can use the `intros` tactic with no input. Try it on these
example : ∀ x : ℝ, 0 < x → x < 2*x := by
  sorry
  done

example : ∀ ε : ℝ, ε > 0 → ε/2 > 0 := by
  sorry
  done
example : ∀ x y z : ℝ, (5*x < 3*y) → (2*y < 3*z) → (10*x < 9*z) := by
  sorry
  done

-- Sometimes `linarith` cannot close inequality goals on its own because the proof relies on some fact which holds in your particular context but no in the general abstract context in which `linarith` operates. For example, in the real numbers we have the theorem `sq_nonneg x : 0 ≤ x^2`, which `linarith` doesn't know about. The `linarith` tactic automatically uses your hypotheses, but you can also give it additional facts by listing them in brackets like this:
example : ∀ x y : ℝ, 2*x*y ≤ x^2 + y^2 := by
  intro x y
  linarith [sq_nonneg (x - y)]

-- Try this one!
example : ∀ x₁ x₂ y₁ y₂ : ℝ, (x₁*y₁ + x₂*y₂)^2 ≤ (x₁^2 + x₂^2)*(y₁^2 + y₂^2) := by
  sorry
  done

-- # Algebra and inequalities by hand
-- In some situations the algebra and inequalities you want to do are too complicated for `ring` or `linarith` to handle alone. Maybe they involve some identities outside the scope of `ring` or use facts that are too hard to pass to `linarith`. In those cases we can use tactics like `calc` and `trans` to break things up into simpler pieces.

-- This example can be solved immediately using a variant on `ring` called `ring_nf`, but for the sake of exposition, let me show you how to do it with `calc`. The `calc` tactic allows you to prove an equality or inequality via a string of steps, similar to how we might when writing a proof. We start with the left hand side, then for each of our intermediate steps, we write `:=` followed by a proof term of that relation. In the subsequent lines we can put an underscore `_` on the left hand side and Lean will fill that in with the right hand side from the above.
example (a b c d e : Nat)
        (h1 : a = b)
        (h2 : b = c + 1)
        (h3 : c = d)
        (h4 : e = 1 + d)
        : a = e := by
        calc
          a = b     := h1 -- Simpler version of `by exact h1`
          _ = c + 1 := h2
          _ = d + 1 := by rw [h3]
          _ = 1 + d := by ring
          _ = e     := by rw [← h4]
        done

-- FYI: The triangle inequality is called `abs_add_le a b : |a + b| ≤ |a| + |b|`
example (x y z : ℝ) : |x - z| ≤ |x - y| + |y - z| := by
  sorry
  done

-- Alternatively, whenever we are trying to prove `a = c` or `a < c` or anything of the form `a ∼ c` where `∼` is a transitive relation, we can use the `trans` tactic to break this into two subgoals. Here are a couple examples

example (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c := by
  -- splits into two goals `a = b` and `b = c`
  trans b
  · assumption
  · assumption

-- Notice that in the above example, both our subgoals were closed by the same tactic `assumption`. There's a slick way to avoid this repetition using the syntax `<;>`. If `tac1` is a tactic which takes our current goal and splits it into some number of subgoals, each of which `tac2` closes, then we can write `tac1 <;> tac2` to automatically apply `tac2` to each subgoal produced by `tac1`. Check it out:

example (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c := by
  trans b <;> assumption
  done

-- Here's an example of `trans` at work on some inequalities
example (x y z : ℝ) (hxy : x < y) (hyz : y < z) : x < z := by
  sorry
  done
