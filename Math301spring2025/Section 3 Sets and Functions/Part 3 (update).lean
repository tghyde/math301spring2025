/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import Library.Theory.S3.P3
/-
## Sets and Functions
## Part 3: Injective, Surjective, Bijective
-/

set_option linter.unusedTactic false
set_option pp.fieldNotation false

variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

namespace Math301

-- I recently learned about the `choose` tactic which makes for a much nicer experience when using the `Classical.choose` function. This allows you to directly extract a right inverse from the assumption that a function is surjective. It also has the nice feature that you avoid having the cumbersome full description of the inverse function in your infoview. Here is a demonstration:

theorem surjective_has_right_inverse'
  (f : X → Y)
  (hf : is_surjective f)
  : has_right_inverse f := by
    choose g hg using hf
    use g
    apply hg
    done
