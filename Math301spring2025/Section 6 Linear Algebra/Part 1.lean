/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
Modified by: Trevor Hyde
-/
import Mathlib.Tactic
set_option linter.unusedTactic false

/-
# Vector spaces

A `vector space` over a field `k` is an additive abelian group `V` together with an operation called `scalar multiplication` or `smul : K × V → V` denoted `a • v` for `a : k` and `v : V`, which satisfy the following axioms:

If `a b : k` and `u v : V`, then
1. `(a + b) • v = (a • v) + (b • v)`
2. `a • (u + v) = (a • u) + (a • v)`
3. `1 • v = v`
4. `(a * b) • v = a • (b • v)`

`Note:` The notation for scalar multiplication is `•` which we type as `\smul`, whereas the `*` notation is reserved for multiplication inside the field `k`.

In Lean, vector spaces go by another name: they're called `modules`. Really, a module is a generalization of a vector space where we allow `k` to be any ring and not just a field. Notice that none of the axioms for a vector space explicitly use the fact that the scalars have division, so they make perfectly good sense with `k` being any ring. That's what we call a module.

However, you should know that the theory of modules is much more challenging, interesting, and nuanced than the theory of vector spaces.
-/

-- To create a variable representing a vector space, we bundle a field and an additive commutative group together into a module like this:
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
variable (a b : k) (u v w : V)

#print Module

/-
For your reference, here are the axioms of a vector space according to Lean

`smul_add : a • (u + v) = a • u + a • v`
`add_smul : (a + b) • v = a • v + b • v`
`one_smul : (1 : k) • v = v`
`smul_smul : a • b • v = (a * b) • v`

Here is a theorems you can use:
`neg_one_smul : -1 • v = -v`
-/

-- Let's prove some basic properties
-- Try using the tactic `abel` to solve goals which are identities that should hold in any additive abelian group.
example : (a - b) • v = a • v - b • v := by
  sorry
  done

example : (0 : k) • v = 0 := by
  sorry
  done

example : a • (0 : V) = 0 := by
  sorry
  done

/-
## Subspaces

The type of subspaces of a vector space is called `Subspace k V`. You
have to mention `k` because `V` does not remember which field it is a vector space with respect to.
-/
-- Let `X` and `Y` be subspaces of `V`
variable (X Y : Subspace k V)


-- Subspaces of a vector space form a complete lattice, so Lean uses lattice notation for them. That is, in order to express that `X ⊆ Y` in Lean we write `X ≤ Y`.

example : Prop :=
  X ≤ Y -- `X ≤ Y` is a true-false statement

example : Subspace k V :=
  X ⊓ Y -- intersection of `X` and `Y`, as a subspace

example : Subspace k V :=
  X ⊔ Y -- `X + Y`, as a subspace. It's the smallest subspace of `V` containing `X` and `Y`, so it's the sup of `X` and `Y` in the lattice of subspaces.

example : Subspace k V :=
  ⊥ -- the 0-dimensional subspace which only contains the `0` vector.

example : Subspace k V :=
  ⊤ -- V considered as a subspace of itself; note that we can't use V to represent this subspace because V is a type, and a subspace of V is a term.

-- For elements of subspaces it's just like sets:
example : Prop :=
  v ∈ X -- the type of `v` is `V`, and the true-false statement is `v ∈ X`.



/-
## Linear Maps

A `linear map` between `k`-vector spaces `V` and `W` is a function `φ : V → W` such that `φ (v₁ + v₂) = φ v₁ + φ v₂` for all `v₁ v₂ ∈ V` and `φ (a • v) = a • φ v` for all `a ∈ k` and `v ∈ V`. These are the functions which may be represented by matrices.

The notation for representing linear maps in Lean is a bit strange. A `k`-linear map from `V` to `W` is a term of type `V →ₗ[k] W`. This is notation `LinearMap (RingHom.id k) V W`, i.e. additive group homs `φ : V → W` such that `φ (a • b) = (id a) • (φ b)`. Note that terms of type `V →ₗ[k] W` are *not* simply functions `V → W`, they're a bundle of data that includes such a function together with the linearity hypotheses.
-/

-- Let `W` be another `k`-vector space
variable (W : Type) [AddCommGroup W] [Module k W]

-- let `φ : V → W` be a `k`-linear map
variable (φ : V →ₗ[k] W)

-- Axioms for a linear map:
example : φ (a • v) = a • φ v :=
  φ.map_smul a v

example : φ (v + w) = φ v + φ w :=
  φ.map_add v w

-- You can take the image and preimage of subspaces along a linear map `φ : V →ₗ[k] W`.
example (X : Subspace k V) : Subspace k W :=
  X.map φ

example (Y : Subspace k W) : Subspace k V :=
  Y.comap φ

-- If `φ : V → W` is a linear map, if `X` is a subspace of `V` and `Y` a subspace of `W`, prove that `φ(X) ⊆ Y` iff `X ⊆ φ⁻¹(Y)`
example (X : Subspace k V) (Y : Subspace k W) : X.map φ ≤ Y ↔ X ≤ Y.comap φ := by
  sorry
  done
