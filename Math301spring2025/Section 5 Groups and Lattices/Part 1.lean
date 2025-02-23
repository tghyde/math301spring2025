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
## Part 1: Introducing Groups and Type Classes
-/

/-
In this section we study `groups` in Lean. Let's give an informal definition of a group in the language of type theory: A `group` is a type `G` together with a binary operation `* : G → G → G`, a unary operation `⁻¹ : G → G` called `inverse`, and a distinguished term `1 : G` called the `identity` such that the following axioms hold:
1. `(Associativity)` ∀ g₁ g₂ g₃ : G, (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃),
2. `(Identity)` ∀ g : G, 1 * g = g * 1 = g,
3. `(Inverses)` ∀ g : G, g * g⁻¹ = g⁻¹ * g = 1.

We declare a type `G` to be a group in Lean as follows:
-/
variable (G : Type) [Group G]

/-
This bracket notation is used to declare that the _type_ `G` is an instance of the _class_ `Group`. The class specifies all the extra structure and axioms that come along with being a group. We can see what all this entails if we `#print` the class `Group`. Put your cursor on the print line to see a bunch of data in your infoview.
-/
#print Group
/-
Let's break this down:
# class Group.{u} (G : Type u) : Type u
# number of parameters: 1
This first line declares the class, describes it as a function which takes in a type `G` in some type universe `Type u` and outputs a new type `Group G` in the same type universe. The second line just tells us that the class takes a single input, in this case the type `G`.

# parents:
#  Group.toDivInvMonoid : DivInvMonoid G
There are many algebraic structures related to groups. Each of these has its own class. In the Lean math library, these classes are layered on top of one another to improve efficiency. This line tells us that the immediate "parent class" of Group in Lean is something called a `DivInvMonoid`. A `monoid` is a just like a group but without necessarily having inverses. In this way, a group is a special kind of monoid. In particular, it is a monoid which happens to have inverses. Try inspecting `#print DivInvMonoid` to see if you can spot the difference between it and `Group`.

# fields:
#  Mul.mul : G → G → G
#  Semigroup.mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)
#  One.one : G
#  MulOneClass.one_mul : ∀ (a : G), 1 * a = a
#  ...
Next we see a bunch of lines following the heading `fields`. This describes all the data being carried around in an instance of `Group`. We see the multiplication operation, the identity, and a bunch of axioms. There's a lot more stuff here than is strictly necessary to define a group, but the point is to have all the most convenient facts and structure right at our fingertips. On the other hand, all this data places a burden on us when we try to construct examples of groups, but we'll talk about that later.

# constructor:
#  Group.mk.{u} {G : Type u} [toDivInvMonoid : DivInvMonoid G] (inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1) : Group G
We then see one long line after the heading `constructor`. This tells us how to make an instance of `Group`. The stuff in brackets tells us that we first have to create a `DivInvMonoid` out of type `G`, and then we have one additional axiom to check about inverses.

# resolution order:
#  Group, DivInvMonoid, Monoid, Inv, Div, Semigroup, MulOneClass, One, Mul
Finally we have a line with heading `resolution order`. Previously we talked about the layers of classes which build up to `Group`. These layers are not necessarily linearly ordered. Some classes could inherit multiple other classes which could then later have a common ancestor. This can potentially cause problems when trying to figure out how to interpret the various `fields`. The `resolution order` specifies the order in which the class `Group` considers its parents in order to figure out how to properly interpret its fields.
-/


-- Let's see groups in action.
example (g : G) : g⁻¹ * g = 1 := by
  -- move your cursor here and check out the infoview
  exact inv_mul_cancel g
-- You'll see there's a line in the infoview that looks like `inst✝ : Group G`. You may have seen this kind of greyed out name for a term before if you've ever accidentally reused a name. The little cross `✝` is a gravestone marking that this term has died (RIP). All this is saying is that `G` is an instance of the class `Group`. We will use that implicitly when we invoke theorems and axioms about groups to apply to `G`, but I don't know that we ever need to explicitly reference this hypothesis, which is why it is dead on arrival.

-- For the next two, solve them by using `exact?` or `apply?`. FYI, you can also try `rw?` or `simp?` to get suggestions for rewriting or simplifying.
example (a b c : G) : a * b * c = a * (b * c) := by
  sorry
  done

example (a : G) : a * 1 = a := by
  sorry
  done

-- Notice that both of these show up in the `fields` section of the `#print Group` line we analyzed above. These are axioms of a group.

-- For the next two, see if you can guess the name of the axiom before using `apply?`. The naming conventions seem annoying at first, but once you get the hang of them, they're not too hard to guess.
example (a : G) : 1 * a = a := by
  sorry
  done

example (a : G) : a * a⁻¹ = 1 := by
  sorry
  done


-- Let's get some practice using the axioms for a group by proving the following generic identities using `rw`.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  sorry
  done

example : a * (a⁻¹ * b) = b := by
  sorry
  done

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  sorry
  done

example : a * b = 1 ↔ a⁻¹ = b := by
  sorry
  done

-- In this one, we need to specify `(1 : G)` since otherwise the expression is ambiguous about what `1` means. Note that we only have to do it for a single `1` since the other one can be inferred from context.
example : (1 : G)⁻¹ = 1 := by
  sorry
  done

example : a⁻¹⁻¹ = a := by
  sorry
  done

-- This one is tricky!
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
  done

/-
In the previous section we introduced the tactic `ring` which could automatically prove algebraic identities which followed from the axioms of a ring. There is a similar tactic called `group` which does the same thing for groups. For example, this gives a one-liner for the previous fact.
-/
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group
  done
-- There is a theorem/algorithm due to Knuth and Bendix which shows that Lean's axioms for a group are sufficient to prove any general group theory identity. That is, the `group` tactic will always work if the identity is true.

-- Try the `group` hammer on this gnarly one.
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by
  sorry
  done

-- We close this section with a tricky problem. I suggest working it on paper before getting lost in the rewrites. You can't use `group` right out of the gate, but try to reduce it to something where you can use `group`.
example (hsq : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  sorry
  done
