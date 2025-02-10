/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
## Analysis
## Part 3: Topology of ℝ
-/

namespace Math301

-- Limit point of a sequence
@[simp]
def seq_limit_point (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∀ m, ∃ n ≥ m, |a n - l| < ε

-- Limit point of a subset of real numbers
@[simp]
def limit_point (U : Set ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ u ∈ U, (u ≠ l) ∧ |u - l| < ε

-- Closed subset of ℝ
@[simp]
def is_closed (U : Set ℝ) : Prop :=
  ∀ u, limit_point U u → u ∈ U

-- Open subset of ℝ
@[simp]
def is_open (U : Set ℝ) : Prop :=
  ∀ v ∈ U, ∃ ε > 0, ∀ u, |u - v| < ε → u ∈ U


-- You can use the `let x := by ...` syntax to locally define variables or functions within a proof. You may find this helpful in the following problem.

-- There exists a sequence with at least two limit points
example : ∃ (a : ℕ → ℝ) (k l : ℝ), k ≠ l ∧ seq_limit_point a k ∧ seq_limit_point a l := by
  sorry
  done

-- Remember: you can use `apply?` if you suspect there may be a theorem in the library which helps you make progress on your goal.

-- Complement of an open set is closed
theorem open_complement_closed
  (U : Set ℝ)
  (hU : is_open U)
  : is_closed Uᶜ := by
    sorry
    done

-- Union of open sets is open
theorem open_union_open
  (U V : Set ℝ)
  (hU : is_open U)
  (hV : is_open V)
  : is_open (U ∪ V) := by
    sorry
    done

-- Set of limit points of a sequence is closed
theorem seq_limit_points_closed
  (a : ℕ → ℝ)
  : is_closed {u | seq_limit_point a u} := by
    sorry
    done

-- This next one is a challenge. If you're behind, it's okay to skip it. I strongly suggest working out a proof on paper first. Try to break down the argument into several steps which you can create as subgoals using the `have` tactic. Before proving each subgoal, check that the pieces all fit together to give you result. Despite being a named theorem, this is something you could prove yourself if you've studied real analysis. I encourage you to try to find and formalize your own proof. If you get stuck, I've posted the proof I used to formalize this on Moodle.
theorem bolzano_weierstrass
  (a : ℕ → ℝ)
  (hbdd : ∃ B, ∀ n, |a n| ≤ B)
  : ∃ u, seq_limit_point a u := by
    sorry
    done
