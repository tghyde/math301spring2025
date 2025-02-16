/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false


theorem bezout (a b : ℕ) : ∃ m n : ℤ, Nat.gcd a b = m * a + n * b := by

done
