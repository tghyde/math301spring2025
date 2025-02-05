/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Library.Theory.S3.P3
import Library.Theory.S3.P4

/-
## Sets and Functions
## Part 5: Equinumerous
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

namespace Math301

-- Now we define what it means for two types to have the same size
def equinumerous (X Y : Type) : Prop :=
  ∃ (f : X → Y), is_bijective f

-- This is an alternative syntax for attaching custom relations to symbols
infix:50 " ∼ " => equinumerous

#check X ∼ Y

-- For the theorems below, we do more than just show the types have the same size: our proofs give an explicit way to transform one type into another.

theorem mul_comm {X Y : Type} : (X × Y) ∼ (Y × X) := by
  -- We first need to define the function. The `use` tactic says what comes next is the function we are looking for, and `by` let's us use tactic mode to construct it. Notice how the goal changes inside the `use`.
  use by
    rintro ⟨x,y⟩
    exact ⟨y,x⟩
  -- For each of these problems, it is simpler to construct the inverse than to argue injective and surjective directly.
  apply inverse_bijective

  -- Now we need to explicitly define the inverse
  use by
    rintro ⟨y,x⟩
    exact ⟨x,y⟩
  -- The goal now looks really ugly, but thankfully this is all formal nonsense
  tauto
  done

-- Try the rest! `tauto` may get stuck if it has to consider cases. You can help it along by "unpacking" inputs
theorem mul_add {X Y Z : Type}
  : (X × (Y ⊕ Z)) ∼ ((X × Y) ⊕ (X × Z)) := by
    sorry
    done

theorem power_add_mull {X Y : Type}
  : (Set (X ⊕ Y)) ∼ ((Set X) × (Set Y)) := by
    sorry
    done

theorem curry {X Y Z : Type}
  : (X × Y → Z) ∼ (X → Y → Z) := by
    sorry
    done

-- This is the set theory version of 2^0 = 1
theorem power_zero : Set Empty ∼ Unit := by
  sorry
  done

end Math301
