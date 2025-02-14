/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false

/-
## Analysis
## Part 3: Topology of ℝ
-/

namespace Math301

-- Limit point of a sequence
@[simp]
def seq_limit_point (a : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∀ m, ∃ n ≥ m, |a n - l| < ε

-- Limit point of a subset of real numbers
@[simp]
def limit_point (U : Set ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ u ∈ U, (u ≠ l) ∧ |u - l| < ε

-- Closed subset of ℝ
@[simp]
def is_closed (U : Set ℝ) : Prop :=
  ∀ u, limit_point U u → u ∈ U

-- Open subset of ℝ
@[simp]
def is_open (U : Set ℝ) : Prop :=
  ∀ v ∈ U, ∃ ε > 0, ∀ u, |u - v| < ε → u ∈ U

-- There exists a sequence with at least two limit points
example : ∃ (a : ℕ → ℝ) (k l : ℝ), k ≠ l ∧ seq_limit_point a k ∧ seq_limit_point a l := by
  let a : ℕ → ℝ := fun n => (-1)^n
  use a
  use 1
  use -1
  constructor
  · norm_num
  · constructor
    · intro ε hε m
      use 2*m
      constructor
      · linarith
      · ring
        norm_num
        linarith
      done
    · intro ε hε m
      use 2*m+1
      constructor
      · linarith
      · ring
        norm_num
        linarith
      done
  done

-- Complement of an open set is closed
theorem open_complement_closed
  (U : Set ℝ)
  (hU : is_open U)
  : is_closed Uᶜ := by
    intro v hv
    by_contra hv'
    have hvU : v ∈ U := Set.not_mem_compl_iff.mp hv'
    have ⟨ε, hε, hv''⟩ := hU v hvU
    have ⟨u,hu₁,hu₂,hu₃⟩ := hv ε hε
    specialize hv'' u hu₃
    contradiction
    done

-- Union of open sets is open
theorem open_union_open
  (U V : Set ℝ)
  (hU : is_open U)
  (hV : is_open V)
  : is_open (U ∪ V) := by
    rintro x (hxU | hxV)
    · have ⟨ε,hε,hU'⟩ := hU x hxU
      use ε
      constructor
      · assumption
      · intro u hu
        left
        apply hU' u hu
        done
      done
    · have ⟨ε,hε,hU'⟩ := hV x hxV
      use ε
      constructor
      · assumption
      · intro u hu
        right
        apply hU' u hu
        done
      done
    done

-- Set of limit points of a sequence is closed
theorem seq_limit_points_closed
  (a : ℕ → ℝ)
  : is_closed {u | seq_limit_point a u} := by
    intro u hu
    simp
    intro ε hε m
    simp at hu
    have ⟨v,hv₁,hv₂,hv₃⟩ := hu (ε/2) (by linarith)
    have ⟨n,hn₁,hn₂⟩ := hv₁ (ε/2) (by linarith) m
    use n
    constructor
    · assumption
    · calc
      |a n - u| = |(a n - v) + (v - u)| := by ring
              _ ≤ |a n - v| + |v - u|   := abs_add_le _ _
              _ < (ε/2) + (ε/2)         := by {
                apply add_lt_add <;> assumption
              }
              _ = ε                     := by ring
    done

theorem bolzano_weierstrass
  (a : ℕ → ℝ)
  (hbdd : ∃ B, ∀ n, |a n| ≤ B)
  : ∃ u, seq_limit_point a u := by
    let b : ℕ → ℝ := by
      intro m
      exact sSup {a n | n ≥ m}
    let c := sInf {b n | n}
    use c
    have ⟨B,hB⟩ := hbdd
    intro ε hε m₀

    have hb_bdd : ∀ m, BddAbove {x | ∃ n ≥ m, a n = x} := by
      intro m
      use B
      rintro y ⟨m',hm'₁,hm'₂⟩
      rw [← hm'₂]
      specialize hB m'
      rw [abs_le] at hB
      exact hB.2
      done

    have hb_nonempty : ∀ m, Set.Nonempty {x | ∃ n ≥ m, a n = x} := by
      intro m
      use a m
      use m

    have hb₁ : ∀ m n, m ≤ n → b m ≥ b n := by
      intro m n hmn
      simp
      refine csSup_le_csSup ?_ ?_ ?_
      · exact hb_bdd m
      · exact hb_nonempty n
      · rintro x ⟨k, hk₁, hk₂⟩
        use k
        constructor
        · linarith
        · assumption
        done
      done

    have hb₂ : ∀ ε > 0, ∃ m₁, ∀ n ≥ m₁, c ≤ b n ∧ b n < c + ε := by
      intro ε₁ hε₁
      refine exists_forall_ge_and ?_ ?_
      · use 0
        intro j hj
        refine Iff.mpr (Real.sInf_le_iff ?_ ?_) ?_
        · use -B
          rintro y ⟨m', hm'⟩
          rw [← hm']
          specialize hB m'
          rw [abs_le] at hB
          have : -B ≤ a m' := hB.1
          trans a m'
          · assumption
          · refine Iff.mpr (Real.le_sSup_iff ?_ ?_) ?_
            · exact hb_bdd m'
            · exact hb_nonempty m'
            · intro ε' hε'
              use a m'
              constructor
              · use m'
              · linarith
              done
          done
        · use b 0
          use 0
          done
        · intro ε' hε'
          use b j
          constructor
          · use j
          · linarith
          done
        done
      · have inf_prop : ∃ x ∈ {x | ∃ n, b n = x}, x < sInf {x | ∃ n, b n = x} + ε₁ := by
          apply Real.lt_sInf_add_pos ?_ hε₁
          use b 0
          use 0
          done
        obtain ⟨x, ⟨n,hn⟩, hx₂⟩ := inf_prop
        use n
        intro j hj
        calc
          b j ≤ b n := by {
            simp at hj
            linarith [hb₁ n j hj]
          }
           _ < c + ε₁ := by {
            rw [hn]
            exact hx₂
           }
        done
      done

    have hb₃ : ∀ ε > 0, ∀ m, ∃ n ≥ m, b m - ε < a n ∧ a n ≤ b m := by
      intro ε₁ hε₁ m
      have sup_prop : ∃ x ∈ {x | ∃ n ≥ m, a n = x}, sSup {x | ∃ n ≥ m, a n = x} - ε₁ < x := by
        apply Real.add_neg_lt_sSup
        · use a m
          use m
          done
        · linarith
          done
        done
      obtain ⟨x,⟨n,hn₁,hn₂⟩,hx'⟩ := sup_prop
      use n
      constructor
      · assumption
      · constructor
        · rw [hn₂]
          exact hx'
        · refine Iff.mpr (Real.le_sSup_iff (hb_bdd m) (hb_nonempty m)) ?_
          intro ε hε
          use a n
          constructor
          · use n
          · linarith
          done
      done

    have ⟨m₁, hm₁⟩ := hb₂ ε hε
    have ⟨n, hn₁, hn₂, hn₃⟩ := hb₃ ε hε (max m₀ m₁)

    use n
    constructor
    · trans max m₀ m₁
      · assumption
      · exact Nat.le_max_left m₀ m₁
      done
    · rw [abs_lt]
      constructor
      · calc
        -ε = (c - ε) - c := by ring
         _ ≤ (b (m₀ ⊔ m₁) - ε) - c := by {
            specialize hm₁ (m₀ ⊔ m₁)
            have : (m₀ ⊔ m₁) ≥ m₁ := Nat.le_max_right m₀ m₁
            linarith [(hm₁ this).1]
         }
         _ < a n - c := by linarith
        done
      · calc
          a n - c ≤ b (m₀ ⊔ m₁) - c := by linarith
                _ < (c + ε) - c     := by {
                  specialize hm₁ (m₀ ⊔ m₁)
                  have : (m₀ ⊔ m₁) ≥ m₁ := Nat.le_max_right m₀ m₁
                  linarith [(hm₁ this).2]
                }
                _ = ε := by ring
        done
      done
    done
