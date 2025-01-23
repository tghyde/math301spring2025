/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.

Based on `Defining Natural Numbers` in Section 7 of `Theorem Proving in Lean 4`
-/

/-
## Natural Numbers
## Part 3: Exponents
-/

import Library.Theory.S2.P1
import Library.Theory.S2.P2

set_option linter.unusedTactic false
set_option pp.fieldNotation false

namespace Math301
namespace Nat

-- Now it's your turn. Give a recursive definition of the power function which intuitively is given by `pow a b := a^b`
def pow (a b : Nat) : Nat :=
  sorry

-- This allows you to use the notation a^b in place of pow a b
instance : Pow Nat Nat where
  pow := pow

theorem pow_zero (a : Nat) : a^zero = one := by
  sorry
  done

theorem pow_succ (a b : Nat) : a^(succ b) = (a^b) * a := by
  sorry
  done

theorem pow_one (a : Nat) :  a^one = a := by
  sorry
  done

theorem pow_two (a : Nat) : a^two = a * a := by
  sorry
  done

theorem pow_add (a b c : Nat) : a^(b + c) = (a^b) * (a^c) := by
  sorry
  done

theorem pow_mul (a b c : Nat) : a^(b * c) = (a^b)^c := by
  sorry
  done

end Nat
end Math301
