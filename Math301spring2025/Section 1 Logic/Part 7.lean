/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Trevor Hyde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Kevin Buzzard
Modified by: Trevor Hyde
-/

import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.unusedTactic false

variable (P Q R S : Prop)

/-
# Logic in Lean
# Part 7: tauto

We learn how to use the `tauto` tactic.

As mentioned in Part 4, `tactics` are metaprograms we use to make writing proofs more efficient. So far, all of our proofs in Lean have used tactics. When we use the keyword `by` at the beginning of a proof, that tells Lean to go into `tactic mode` where tactics may be used. Without this keyword we would have to construct our proofs from scratch using pure Lean code. Sometimes, for very basic proofs, this can be more efficient.
-/

example : (P ∧ Q) → (Q ∧ P) := -- Notice there is no `by` here, which tells Lean we are going to construct our proof directly.
λ h : P ∧ Q ↦ ⟨h.2, h.1⟩       -- The λ symbol tells Lean we are constructing a "function" with input `h` which has type `P ∧ Q`.
                               -- Here we use the \mapsto ↦ arrow, and then specify how the function is defined.

-- On the other hand, there are also more sophisticated tactics which can save us a lot of effort when it comes to filling in details of our proofs. For example, the `tauto` tactice (short for `tautological`) can automatically prove basic statements of propositional logic. I expect that `tauto` can automatically prove every proposition in Section 1. Here are some examples picked from various parts:

example : P → Q → P := by
  tauto
  done

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  tauto
  done

example : (¬Q → ¬P) → P → Q := by
  tauto
  done

example : (P ∧ Q → R) → P → Q → R := by
  tauto
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  tauto
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  tauto
  done

-- Perhaps you're asking yourself: if it was that easy, why did we spend all that time doing it the "hard way"? The point was to develop your basic Lean skills so you'll be prepared to tackle more challenging proofs. Once you have mastered proving simple propositional statements, feel free to use `tauto` to streamline your proofs.
