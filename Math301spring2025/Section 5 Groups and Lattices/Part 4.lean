/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
Modified by: Trevor Hyde
-/
import Mathlib.Tactic

set_option linter.unusedTactic false

/-
## Groups and Lattices
## Part 4: Group Homomorphisms
-/

/-
In order to study the relationship between groups we introduce the "structure preserving maps" between them, called `homomorphisms`. If `G` and `H` are groups, then a function `φ : G → H` is called a `homomorphism` if for all `a b : G` we have `φ(a * b) = φ(a) * φ(b)` and `φ(1) = 1`. In Lean there is a special syntax for homomorphisms, we write `φ : G →* H` to denote that the function `φ` is a homomorphism from `G` to `H`.
-/

section Homomorphisms

variable {G H K : Type} [Group G] [Group H] [Group K]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)
-- If you hover your cursor over the `→*` symbol it will tell you it is a "monoid homomorphism". A monoid is an algebraic structure like a group but without the assumption that every element is invertible. Hence a group is a monoid with the extra property that every element has an inverse.

-- Just as we did with subgroups, we can use the dot notation to extract facts about `φ`. For example, here is the fact that `φ` respects products.
example (a b : G) : φ (a * b) = φ a * φ b := by
  exact φ.map_mul a b

-- Note: You can also use these theorems with `rw`.
example (a b : G) : φ (a * b) = φ a * φ b := by
  rw [φ.map_mul a b]

-- Actually, when using them in `rw`, you don't even need to specify the `φ` or the `a b` because Lean can figure it out.
example (a b : G) : φ (a * b) = φ a * φ b := by
  rw [map_mul]

-- See if you can guess the name of the theorems you need to solve this one.
example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  sorry
  done


-- Group homomorphisms, like functions, are `extensional`. That is, two group homomorphisms are the same if and only if they have the same outputs at all inputs. Hence to prove two homomorphisms are the same, we can start by using the `ext` tactic.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  sorry
  done

-- Let's show that the composition of two homomorphisms is again a homomorphism. This example is a bit different than other results we have proved. For one, we are both constructing the composition and proving it is a homomorphism simultaneously. To get started, click the underscore after the `:=`. Doing so, you should see a lightbulb show up (it's blue on my computer) on the next line. Click it, and select the option `Generate a skeleton for the structure under construction`. This will fill in the outline of what you need to provide. For each blank, follow your training. Note: You cannot directly compose `φ` and `ψ` since they aren't technically functions; try `ψ.comp φ`.
example (φ : G →* H) (ψ : H →* K) : G →* K := _

-- The kernel of a homomorphism `φ : G → H` is the subgroup `φ.ker = {x | φ x = 1}`.
example (φ : G →* H) (x : G) : x ∈ φ.ker ↔ φ x = 1 := by rfl

def is_injective (φ : G →* H) : Prop :=
  ∀ g₁ g₂ : G, φ g₁ = φ g₂ → g₁ = g₂

-- The "bottom symbol" `⊥` is also part of lattice notation. It represents the smallest element in a lattice. In the context of subgroups of `G` the `⊥` is the `trivial subgroup` which consists of only the trivial element.
example (φ : G →* H) : is_injective φ ↔ φ.ker = ⊥ := by
  sorry
  done

-- The image of `φ`, denoted `φ.range` is defined as you might expect.
example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y := by rfl

-- `Subgroup.map` is used for the image of a subgroup under a group hom
example (φ : G →* H) (S : Subgroup G) : Subgroup H :=
  S.map φ

example (φ : G →* H) (S : Subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y := by rfl

-- and `Subgroup.comap` is used for the preimage of a subgroup under a group hom.
example (φ : G →* H) (S : Subgroup H) : Subgroup G :=
  S.comap φ

example (φ : G →* H) (T : Subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T := by rfl

-- Let's prove some facts about these constructions.

-- If `S ≤ T` are subgroups of `H` then `φ⁻¹(S) ≤ φ⁻¹(T)` as subgroups of `G`.
example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  sorry
  done

-- If `S ≤ T` are subgroups of `G` then `φ(S) ≤ φ(T)` as subgroups of `H`.
example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ := by
  sorry
  done

-- The composite of preimages is the preimage of the composite.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : U.comap (ψ.comp φ) = (U.comap ψ).comap φ := by
  sorry
  done
