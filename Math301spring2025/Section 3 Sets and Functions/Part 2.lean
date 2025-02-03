/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/

import Mathlib.Tactic

/-
## Sets and Functions
## Part 2: Images and Preimages
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

variable (X Y Z : Type) (f : X → Y) (g : Y → Z) (A : Set X) (B : Set Y) (C : Set Z)

/-
# Set Comprehension

In mathematics, the most common way we define a set is via `set comprehension`. This is where we have some set `X` and we describe a subset `A ⊆ X` like this `A = {x : X | P x}` where `P : X → Prop` is some predicate. We read this is "`A` is the set of all `x` in `X` such that `P x` is true." For example, the set `E` of even natural numbers may be described by `E = {n : Nat | ∃ m : Nat, n = 2*m}`. Happily, this notation works perfectly well in Lean.
-/

def E := {n : Nat | ∃ m : Nat, n = 2*m}

#check E -- E : Set ℕ

example : 24 ∈ E := by
  use 12
  done

/-
# Images of Functions

Suppose that `f : X → Y` is a function and `A : Set X`. The `image` of `A` under `f`, which we would typically denote `f(A)` is defined to be `f(A) = {y | ∃ x ∈ A, f(x) = y}`. However, in Lean we cannot write `f(A)` since `A` does not have the correct type for an input of `f`. Instead Lean uses the notation `f '' A` to denote the image of `A` under `f`.
-/

example : f '' A = {y | ∃ x ∈ A, f x = y} := by
  rfl

/-
# Preimages of Functions

Next suppose that `f : X → Y` is a function and `B : Set Y`. The `preimage` of `B` under `f`, which we would typically denote `f⁻¹(B)` is defined to be `f⁻¹(B) = {x | f x ∈ B}`. However, in Lean the `⁻¹` symbol is reserved for literal inverses (in the sense of group theory). So instead we use `f ⁻¹' B` to denote the preimage of `B` under `f`.
-/

example : f ⁻¹' B = {x | f x ∈ B} := by
  rfl

-- Some problems for you to practice

example : A ⊆ f ⁻¹' (f '' A) := by
  sorry
  done

example : f '' (f ⁻¹' B) ⊆ B := by
  sorry
  done

example : f '' A ⊆ B ↔ A ⊆ f ⁻¹' B := by
  sorry
  done

-- Now let's try composition: Given `f : X → Y` and `g : Y → Z`, we have `g ∘ f : X → Z`
#check g ∘ f

-- Identities about sets and functions which only use the `∀` quantifier can (mostly/all?) be proved by `tauto`
example : (g ∘ f) ⁻¹' C = f ⁻¹' (g ⁻¹' C) := by
  sorry
  done

-- However, `tauto` won't work on statements that involve `∃`. Checking a `∃` statement involves a potentially infinite amount of work, looking for the example, so cannot be blindly auotmated in the same way oteher tautologies can.

-- Note: You can use the `simp` tactic to replace complicated expressions with simplified ones. For example, if you have a goal of the form `(g ∘ f) a = c`, then applying `simp` changes the goal to `g (f a) = c`. This can be useful when you want to use `rw`, since `rw` only works up to syntactic equality instead of semantic equality.
example : (g ∘ f) '' A = g '' (f '' A) := by
  sorry
  done

-- Set operations behave well under preimages
-- Hint: these each have a one line proof
example (B₁ B₂ : Set Y) : f ⁻¹' (B₁ ∩ B₂) = (f ⁻¹' B₁) ∩ (f ⁻¹' B₂) := by
  sorry
  done

example (B₁ B₂ : Set Y) : f ⁻¹' (B₁ ∪ B₂) = (f ⁻¹' B₁) ∪ (f ⁻¹' B₂) := by
  sorry
  done

example (B₁ B₂ : Set Y) : f ⁻¹' (B₁ \ B₂) = (f ⁻¹' B₁) \ (f ⁻¹' B₂) := by
  sorry
  done

-- Images are a bit more subtle
example (A₁ A₂ : Set X) : f '' (A₁ ∪ A₂) = (f '' A₁) ∪ (f '' A₂) := by
  sorry
  done

example (A₁ A₂ : Set X) : f '' (A₁ ∩ A₂) ⊆ (f '' A₁) ∩ (f '' A₂) := by
  sorry
  done

/-
Let's prove that the containment `f(A₁ ∩ A₂) ⊆ f(A₁) ∩ f(A₂)` cannot be upgraded to an equality. To do so, we just need to construct a counterexample.

Here's the idea: If we let `const` be a constant function and let `A₁` and `A₂` be any pair of disjoint sets, then `A₁ ∩ A₂ = ∅` while their images are identical.
-/

-- We will build our sets out of natural number for simplicity. Let's first define our function.
def const : ℕ → ℕ :=
    fun _ => 0

example : ∃ (X Y : Type) (A₁ A₂ : Set X) (f : X → Y),
  f '' (A₁ ∩ A₂) ≠ (f '' A₁) ∩ (f '' A₂) := by
  use ℕ
  use ℕ
  -- If Lean gets confused about what type something should be, you can always help it along.
  use ({0} : Set ℕ)
  use ({1} : Set ℕ)
  use const
  have h₀ : {0} ∩ {1} = (∅ : Set ℕ) := by
    sorry
    done

  have h₁ : const '' ({0} ∩ {1}) = (∅ : Set ℕ) := by
    -- After the `rw`, the goal looks like it *should* be easy, although it isn't clear what the right thing to type should be. Try using the `apply?` tactic to get suggestions. If you see one that starts with `exact`, then that will immediately solve your goal. Otherwise you may see a bunch of options that start with `apply`. Before blindly using these, take a look at them to see if they are really making progress towards your goals.
    rw [h₀]
    sorry
    done
  -- Try `apply?` for these steps
  have h₂ : const '' {0} = {0} := by sorry
  have h₃ : const '' {1} = {0} := by sorry

  -- Now put together these hypotheses to finish the proof
  sorry
  done
