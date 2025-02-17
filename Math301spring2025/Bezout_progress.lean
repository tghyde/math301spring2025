/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false


theorem bezout (a b : ℕ) : ∃ m n : ℤ, Nat.gcd a b = m * a + n * b := by
  if ha : a = 0 then
    rw [ha]
    simp
    use 1
    simp
    done
  else


  let G := {g : ℕ | (∃ m n : ℤ, g = m * a + n * b) ∧ (g > 0)}
  let g := sInf G

  have hg : g ∈ G := by
    apply Nat.sInf_mem
    unfold Set.Nonempty G
    use a
    constructor
    · use 1
      use 0
      simp
      done
    · exact Nat.zero_lt_of_ne_zero ha
      done
    done

  have ⟨⟨m,n,hmn⟩,hgp⟩ := hg

  suffices hgcd : Nat.gcd a b = g by
    rw [hgcd]
    use m
    use n
    done

  have hga : g ∣ a := by
    let r := a % g
    have hr : g * (a / g) + r = a := by apply Nat.div_add_mod
    -- Goal: show r = 0
    rw [Nat.dvd_iff_mod_eq_zero]
    by_contra hr0
    have hrp : r > 0 := by
      exact Nat.zero_lt_of_ne_zero hr0

    have hrmn : ∃ m n : ℤ, r = m*a + n*b := by
      sorry

    have hrG : r ∈ G  := by
      exact ⟨hrmn,hrp⟩

    have hrg₁ : g ≤ r := by sorry

    have hrg₂ : r < g := by sorry

    linarith
    done

  have hgb : g ∣ b := by sorry

  have hc : ∀ (c : ℕ), c ∣ a → c ∣ b → c ∣ g := by
    intro c hca hcb
    have ⟨A, hA⟩ := hca
    have ⟨B, hB⟩ := hcb
    zify at hA hB ⊢
    rw [hmn, hA, hB]
    use ↑A*m + ↑B*n
    ring
    done

  rw [Nat.gcd_eq_iff]
  exact ⟨hga, hgb, hc⟩

  done
