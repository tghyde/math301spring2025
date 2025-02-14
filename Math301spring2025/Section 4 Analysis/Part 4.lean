/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Library.Theory.S4.P2
import Library.Theory.S4.P3

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
## Analysis
## Part 4: Continuity
-/

namespace Math301

def is_continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, |x - y| < δ → |f x - f y| < ε

theorem comp_continuous
  (f g : ℝ → ℝ)
  (hf : is_continuous f)
  (hg : is_continuous g)
  : is_continuous (f ∘ g) := by
    sorry
    done

theorem continuous_inv_open
  (f : ℝ → ℝ)
  (hf : is_continuous f)
  (U : Set ℝ)
  (hU : is_open U)
  : is_open (f⁻¹' U) := by
    sorry
    done

-- You might run into an annoying issue where you want to apply an implication, but your goal has the form `|x - y| < ε` for some `x,y` and your hypothesis has the form `|y - x| < ε`. I suggest writing a helper function `have rev {x y : ℝ} : |x - y| = |y - x|` which help you reverse these. You can also find the theorem in mathlib, but it could be good practice to write your own :)
theorem cont_converge
  (f : ℝ → ℝ)
  (hf : is_continuous f)
  (a : ℕ → ℝ)
  (l : ℝ)
  (ha : tends_to a l)
  : tends_to (f ∘ a) (f l) := by
    sorry
    done

def pw_tends_to (a : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x, ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n x - f x| < ε

def uniformly_tends_to (a : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ x, ∀ n ≥ N, |a n x - f x| < ε

theorem uniform_implies_pw
  (a : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (hu : uniformly_tends_to a f)
  : pw_tends_to a f := by
    sorry
    done

theorem uniform_of_continuous
  (a : ℕ → ℝ → ℝ)
  (f : ℝ → ℝ)
  (hu : uniformly_tends_to a f)
  (ha : ∀ n, is_continuous (a n))
  : is_continuous f := by
    sorry
    done

def is_disconnected (A : Set ℝ) : Prop :=
   ∃ (U V : Set ℝ), is_open U ∧ is_open V ∧ (U ∩ V = ∅) ∧ (A = (U ∩ A) ∪ (V ∩ A)) ∧ (U ∩ A ≠ ∅) ∧ (V ∩ A ≠ ∅)

def is_connected (A : Set ℝ) : Prop :=
  ¬ is_disconnected A

theorem continuous_connected
  (f : ℝ → ℝ)
  (hf : is_continuous f)
  (A : Set ℝ)
  (hA : is_connected A)
  : is_connected (f '' A) := by
    sorry
    done
