/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

/-
## Sets and Functions
## Part 3: Injective, Surjective, Bijective
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
In this part we get practice working with functions. First we define the notions of injectivity, surjectivity, and bijectivity.

Variables automatically get added to the context of any theorem or definition in which they are used. Putting them in curly braces allows them to be inferred when possible, so you don't have to explicitly give them as input.
-/

variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

namespace Math301

def is_injective (f : X → Y) : Prop :=
  ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂

def is_surjective (f : X → Y) : Prop :=
  ∀ y, ∃ x, f x = y

def is_bijective (f : X → Y) : Prop :=
  is_injective f ∧ is_surjective f


-- First let's prove these properties are stable under composition.
-- When there are a lot of hypotheses, you can put things on separate lines to make it more readable
theorem comp_injective
  (hf : is_injective f)
  (hg : is_injective g)
  : is_injective (g ∘ f) := by
    intro x₁ x₂ hgf
    apply hf
    apply hg
    exact hgf
    done

theorem comp_surjective
  (hf : is_surjective f)
  (hg : is_surjective g)
  : is_surjective (g ∘ f) := by
    intro z
    cases' hg z with y hy
    cases' hf y with x hx
    use x
    simp
    rw [hx, hy]
    done

theorem comp_bijective
  (hf : is_bijective f)
  (hg : is_bijective g)
  : is_bijective (g ∘ f) := by
    constructor
    · exact comp_injective hf.1 hg.1
    · exact comp_surjective hf.2 hg.2
    done

def is_left_inverse (f : X → Y) (g : Y → X) : Prop :=
  ∀ x, g (f x) = x

def is_right_inverse (f : X → Y) (g : Y → X) : Prop :=
  ∀ y, f (g y) = y

def is_inverse (f : X → Y) (g : Y → X) : Prop :=
  is_left_inverse f g ∧ is_right_inverse f g

def has_left_inverse (f : X → Y) : Prop :=
  ∃ g : Y → X, is_left_inverse f g

def has_right_inverse (f : X → Y) : Prop :=
  ∃ g : Y → X, is_right_inverse f g

def has_inverse (f : X → Y) : Prop :=
  ∃ g : Y → X, is_inverse f g

-- Here we demonstrate how to use the `calc` tactic to prove a string of equalities
theorem has_left_inverse_injective
  (f : X → Y)
  (hf : has_left_inverse f)
  : is_injective f := by
    cases' hf with g hg
    intro x₁ x₂ hf12
    calc
      x₁ = g (f x₁) := by rw [hg]
       _ = g (f x₂) := by rw [hf12]
       _ = x₂       := by rw [hg]
    done

theorem has_right_inverse_surjective
  (f : X → Y)
  (hf : has_right_inverse f)
  : is_surjective f := by
    intro y
    cases' hf with g hg
    use g y
    exact hg y
    done

theorem inverse_bijective
  (f : X → Y)
  (hf : has_inverse f)
  : is_bijective f := by
    cases' hf with g hg
    constructor
    · apply has_left_inverse_injective f
      use g
      exact hg.1
      done
    · apply has_right_inverse_surjective f
      use g
      exact hg.2
      done
    done

/-
We have proved that invertible functions are always bijections. The reverse is also true, but the proofs are more complicated. In particular, they require `classical logic`. There are generally speaking two kinds of logic: `classical logic` and `constructive logic`. Classical logic is the common logic we use in mathematics, it is the default unless otherwise specified. Constructive logic refers to a weaker form of logic which *does not* include
1. The Law of Excluded Middle: `∀ P : Prop, P ∨ ¬ P`,
2. Double Negation Elimination: `∀ P : Prop, ¬¬ P ↔ P`.
Constructive logic captures the reasoning of `constructive proofs`. The idea is that if we say that something exists, then we need to provide an actual construction. In other words, you cannot prove something exists by contradiction. Proof by contradiction, in general, does not work in constructive logic.

Why limit ourselves with constructive logic? There are lots of good, practical reasons and interesting theoretical reasons. Most simply: constructive proofs can be automatically turned into algorithms. Constructive logic is the default in Lean. We can use classical logic, but we have to do so explicitly.

For example, suppose `f : X → Y` is a function and suppose that `hf : is_surjective f`, which is a proof that `f` is surjective. Hence `hf : ∀ y, ∃ x, f x = y`. If we try to use this to construct a right inverse `g : Y → X` of `f`, then we need to *choose* a specific `x` for each `y` so that `g y := x`. However, the assertion that such an `x` exists for each `y` is weaker than saying we have some effective method of constructing `x` from `y`.

The proof below demonstrates how we can use the `Classical.choose` function to explicitly use classical logic to construct a right inverse.
-/

theorem surjective_has_right_inverse
  (f : X → Y)
  (hf : is_surjective f)
  : has_right_inverse f := by
    use (fun y => Classical.choose (hf y))
    intro y
    simp
    -- `Classical.choose_spec` recovers the defining property of the thing we have chosen. In this case, we chose an `x₀` such that `f x₀ = y`
    rw [Classical.choose_spec (hf y)]
    done

-- There's another subtlety that arises when you try to show that injective functions have a left inverse. Suppose `f : X → Y` is injective, and we want to construct a left inverse `g : Y → X`. It is clear how we should define `g` on the image of `f`, but what about at those `y : Y` which are not in the image? Where do we send them? Well, it doesn't really matter, but we have to choose somewhere to send them. Thus we again need to make a choice. But what if `X` is empty? There are no functions from a nonempty set to the emptyset. So we include the extra hypothesis that `X` is non-empty.
theorem injective_has_left_inverse
  (f : X → Y)
  (hf : is_injective f)
  (x₀ : X)
  : has_left_inverse f := by
    use (fun y => by
      by_cases h : ∃ x, f x = y
      · exact Classical.choose h
        done
      · use x₀
        done
      done)
    intro x
    simp
    have h : ∃ x', f x' = f x := by use x
    apply hf
    rw [Classical.choose_spec h]
    done

-- Let's put it all together!
-- For part of the argument, you will need to split into cases depending on whether or not `X` is empty. The way to express this is `X → False`. This is a mental tongue twister: Note that `False` is a type with no terms. If `X` has terms, then it is impossible to construct a function of type `X → False`. On the other hand, if `X` has no terms, then there is a unique term of type `X → False`, namely the function that does nothing to nothing :).

theorem bijective_has_inverse
  (f : X → Y)
  (hf : is_bijective f)
  : has_inverse f := by
    have h₁ : has_right_inverse f := by
      apply surjective_has_right_inverse f hf.2
      done
    cases' h₁ with g hg
    use g
    constructor
    · intro x
      apply hf.1
      rw [hg]
      done
    · assumption
      done
    done

end Math301
