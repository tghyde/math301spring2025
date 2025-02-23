/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
Modified by: Trevor Hyde
-/
import Mathlib.Tactic

set_option linter.unusedTactic false
set_option pp.fieldNotation false
/-
## Groups and Lattices
## Part 2: Partial Orders and Lattices
-/

namespace Math301
/-
## Partial Orders

A `partial order` is a type `X` with some an ordering relation `≤ : X → X → Prop` which for each `a b : X` satisfies the following axioms:

`le_refl a : a ≤ a`
`le_antisymm : a ≤ b → b ≤ a → a = b`
`le_trans : a ≤ b → b ≤ c → a ≤ c`

The reason these are called *partial* orders, as opposed to a `total order` is that we do not have `trichotomy`. That is, it is not necessarily the case that `a ≤ b` or `b ≤ a`; there may be some pairs of elements which cannot be compared.

The natural orderings on the integers and real numbers are partial orders, but they also satisfy trichotomy. The most natural example of a partial order that is not a total order is `Set X`. Given `A B : Set X` we say `A ≤ B` if `A ⊆ B`. Think through why this satisfies the axioms above.
-/

-- Let `X` be a partial order.
variable (X : Type) [PartialOrder X]

-- You can prove transitivity directly using the axiom
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

-- or you can use the `trans` tactic
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  · exact hab
  · exact hbc

-- or you can use a `calc` block
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  calc
    a ≤ b := hab
    _ ≤ c := hbc

-- Let a,b,c,d be arbitrary elements of `X`
variable (a b c d : X)

-- Try proving these basic facts about partial orders
example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  sorry
  done

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  sorry
  done

/-
A `lattice` is a partial order `X` where any two elements `a b : X` have a least upper bound `a ⊔ b` and a greatest lower bound `a ⊓ b`. These elements satisfy the following properties:

`le_sup_left : a ≤ a ⊔ b`
`le_sup_right : b ≤ a ⊔ b`
`sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c`

`inf_le_left : a ⊓ b ≤ a`
`inf_le_right : a ⊓ b ≤ b`
`le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c`

# Ex 1.
The real numbers `ℝ` form a lattice. Given `a b : ℝ` we define `a ⊔ b := max a b` and `a ⊓ b := min a b`.

# Ex 2.
`Set X` forms a lattice. Given `A B : Set X` we define `A ⊔ B := A ∪ B` and `A ⊓ b := A ∩ B`. This example is the motivation for the notation.

# Ex 3.
Let `V` denote a vector space. Then `Subspace V`, the type of subspaces of `V`, forms a lattice. This one is more subtle than the others. Given `U W : Subspace V`, we define `U ⊓ W := U ∩ W`, but we cannot define `U ⊔ W := U ∪ W`, since the union of subspaces is typically not a subspace. Instead we define `U ⊔ W := U + W`, the sum of the subspaces `U` and `W`.
-/

-- Let L be a lattice, and let a,b,c be elements of L
variable {L : Type} [Lattice L] {a b c : L}

-- Hint: start with `apply le_antisymm`
example : a ⊔ b = b ⊔ a := by
  sorry
  done


example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  sorry
  done

theorem inf_le_inf_left (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  sorry
  done

theorem sup_le_sup_left (h : b ≤ c) : a ⊔ b ≤ a ⊔ c := by
  sorry
  done

-- `inf_le_inf_left`, proved above, is helpful here.
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  sorry
  done

example : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry
  done

theorem sup_inf_self : (a ⊔ b) ⊓ a = a := by
  sorry
  done

theorem inf_sup_self : a ⊓ b ⊔ a = a := by
  sorry
  done


-- This one is tricky, try it on paper first. You may find the theorems `inf_assoc`, `sup_assoc`, `inf_comm`, and `sup_comm` helpful.
example :
  (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
  done

/-

# Complete lattices
A lattice has sups and infs for all subsets with 2 elements. A `complete lattice` has sups and infs for *every* subset (including infinite ones). An example would be `Set X`. Other examples: all subgroups of a group, all subspaces of a vector space (and all subrings of a ring, all subfields of a field...). A non-example is the real numbers: we do say that the reals are "complete" but we're talking about a different kind of completeness here (an order-theoretic concept, not a metric space concept), and indeed unbounded subsets of ℝ like the natural numbers do *not* have a sup. However the closed interval `[0,1]` would be an example of a complete lattice in this sense.

If `L` is a complete lattice, and `S : Set L` is a subset of `L`, then its sup is `sSup S` (the little `s` stands for "set") and its inf is `sInf S`. Here's the basic API for `sSup`:

`le_sSup : a ∈ S → a ≤ Sup S`
`sSup_le : (∀ (b : L), b ∈ S → b ≤ a) → sSup S ≤ a`

I'll let you guess the analogous names for `sInf`.

A special case: the empty set has a `sSup` and and an `sInf`, and if you think carefully about this then you'll discover that this means that the lattice has a least element and a greatest element. These elements are called `⊥` and `⊤` respectively, pronounced `bottom` and `top`.

`sSup_empty : Sup ∅ = ⊥`

See if you can prove basic things about `⊥` and `sSup` just using the API for `sSup`.
All these results are in the library, but it's a good exercise to prove them from
the axioms directly.
-/

-- Let `L` be a complete lattice and say `a` is a general element of `L`
variable {L : Type} [CompleteLattice L] {a : L}

-- These can all be found in mathlib, but see if you can prove them from the axioms.

theorem bot1 : ⊥ ≤ a := by
  sorry
  done

example : a ≤ ⊥ ↔ a = ⊥ := by
  sorry
  done

example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T := by
  sorry
  done

end Math301
