/-
## Natural Numbers
## Part 4: Inequalities & Division with Remainder
-/


import Library.Theory.S2.P1
import Library.Theory.S2.P2
import Library.Theory.S2.P3

namespace Math301
namespace Nat

-- Next we use addition in order to define the "less than" relation `lt`. Unlike our other definitions, this one is not defined recursively. We can still think of `lt` as a binary operation which takes in two inputs, but now instead of outputting a natural number, it output a boolean value of `True` or `False`. That's why `lt a b : Prop`, which means that the expression `lt a b` has type `Prop`, which is Lean's way of saying a boolean.
def lt (a b : Nat) : Prop :=
  ∃ (c : Nat), c ≠ zero ∧ a + c = b

-- Another interesting feature of this definition is the use of the existential quantifier. This means that when we want to directly prove a goal of the form `a < b`, we will need to employ the `use` tactic to tell Lean what the `c` value should be such that `a + c = b`.

-- Can you guess what this does?
instance : LT Nat where
  lt := lt

-- To warm-up, give a definition of "less than or equal to" ≤ `le`
def le (a b : Nat) : Prop :=
  a < b ∨ a = b

instance : LE Nat where
  le := le

theorem lt_def (a b : Nat) : (∃ (c : Nat), c ≠ zero ∧ a + c = b) → a < b := by
  intro h
  assumption
  done

theorem le_def (a b : Nat) : a < b ∨ a = b ↔ a ≤ b := by
  exact Iff.symm (Eq.to_iff rfl)
  done

theorem zero_lt_pos (a : Nat) : a ≠ zero → zero < a := by
  intro ha
  apply lt_def
  use a
  exact ⟨ha, zero_add a⟩
  done


-- The last two theorems should be more of a challenge. I suggest sketching out the proof on paper first before you embark on the formalization.
theorem lt_succ_le (a b : Nat) : a < b → succ a ≤ b := by
  intro h
  rw [← le_def]
  obtain ⟨c, hc₁, hc₂⟩ := h
  by_cases hc : c = one
  · right
    rw [← hc₂, hc, add_one]
  · left
    use pred c
    constructor
    · by_contra h'
      have hz : zero = pred one := by rfl
      apply hc
      apply pred_inj
      · assumption
      · exact one_ne_zero
      · exact h'
      done
    · calc
        succ a + pred c = a + one + pred c := by rfl
        _ = a + (pred c + one) := by rw [add_assoc, add_comm one]
        _ = a + succ (pred c) := by rfl
        _ = a + c := by rw [succ_pred c (hc₁)]
        _ = b := by exact hc₂
    done
  done


-- Good luck!
-- Hint: `induction'` on `a`
theorem div_with_rem (a b : Nat) : b ≠ zero → ∃ (q r : Nat), (a = q * b + r ∧ r < b) := by
  intro hb
  induction' a with a ih
  · use zero
    use zero
    rw [zero_mul, zero_add]
    exact ⟨rfl, zero_lt_pos b hb⟩
    done
  · obtain ⟨q, r, hqr, hr⟩ := ih
    by_cases h : succ r = b
    · use succ q
      use zero
      rw [add_zero]
      constructor
      · calc
          succ a = a + one := by rfl
          _ = q * b + r + one := by rw [hqr]
          _ = q * b + (succ r) := by rw [add_assoc, ← add_one]
          _ = q * b + b := by rw [h]
          _ = (q + one) * b := by
            {
              nth_rw 2 [← one_mul b]
              rw [add_mul]
            }
          _ = (succ q) * b := by rfl
        done
      · exact zero_lt_pos b hb
        done
      done
    · use q
      use (succ r)
      constructor
      · calc
          succ a = a + one := by rfl
          _ = q * b + r + one := by rw [hqr]
          _ = q * b + (succ r) := by rw [add_assoc, ← add_one]
        done
      · have hs : succ r ≤ b := by exact lt_succ_le r b hr
        rw [← le_def] at hs
        cases' hs with h₁ h₂
        · assumption
        · by_contra hc
          exact h h₂
        done
      done
    done
  done

end Nat
end Math301
