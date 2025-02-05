/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Library.Theory.S3.P3

/-
## Sets and Functions
## Part 4: Finite vs Infinite
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

namespace Math301

-- How do we compare the size of two sets? If the sets are finite, then we could simply count the elements to get natural numbers and the compare the natural numbers. But what if the sets are infinite? One brilliant way to do this, which I believe goes back to Georg Cantor, is to use injective functions to compare the size of sets. Namely, if `f : X → Y` is an injective function, then `X` can map into a part of `Y`, hence `Y` should be at least as big as `X`. Hence `X ≤ Y`

def le (X Y : Type) : Prop :=
  ∃ f : X → Y, is_injective f

instance : LE Type where
  le := le

-- Now we can use the `≤` notation with types
#check X ≤ Y

-- As a first example, we can define infinite types by comparison with the natural numbers.
def is_infinite (X : Type) : Prop := ℕ ≤ X

-- `Note:` We are no longer using the version of `Nat` we constructed in Section 2. For the sake of convenience of using actual numbers and the results in the library, we will now use the built-in natural numbers. Almost all the theorems we proved in Section 2 have the same name as the functions in the library.

-- We then define finite to mean the opposite of infinite
def is_finite (X : Type) : Prop := ¬ is_infinite X

-- The following two results demonstrate how to use this definition of infinite. You can use theorems and definitions from `Part 3`.
theorem infinite_injective
  (f : X → Y)
  (hf : is_injective f)
  (hX : is_infinite X)
  : is_infinite Y := by
    sorry
    done

-- `Hint:`If `g` is a right inverse of `f`, then `f` is a left inverse of `g`.
theorem infinite_surjective
  (f : X → Y)
  (hf : is_surjective f)
  (hY : is_infinite Y)
  : is_infinite X := by
    sorry
    done

-- The next two should be quick consequences of the results you just proved.
theorem finite_surjective
  (f : X → Y)
  (hf : is_surjective f)
  (hX : is_finite X)
  : is_finite Y := by
    sorry
    done

theorem finite_injective
  (f : X → Y)
  (hf : is_injective f)
  (hY : is_finite Y)
  : is_finite X := by
    sorry
    done


-- The `power set` of X, denoted `Set X` is the type of all subsets of `X`. The way this is encoded in Lean is that `Set X := X → Prop`. The idea is that a subset can be encoded as a function `f : X → Prop` which for each term of type `X` spits out either true or false depending on whether or not it belongs to the subset.

-- Here we show that the power set function is increasing
theorem injective_power_set (X : Type) : X ≤ Set X := by
  sorry
  done

-- Next we show that for *any* type `X`, the power set `Set X` is strictly larger. This is true even for infinite sets! This is how we know there must be different sizes of infinity.

-- This proof is tricky!
-- `Hint:` Consider the set `D := {x : X | x ∉ f x}`.
theorem not_surjective_power_set
  {X : Type}
  (f : X → Set X)
  : ¬ is_surjective f := by
  sorry
  done

end Math301
