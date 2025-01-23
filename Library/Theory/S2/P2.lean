/-
Copyright (c) 2025 Trevor Hyde. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.

Based on `Defining Natural Numbers` in Section 7 of `Theorem Proving in Lean 4`
-/

/-
## Natural Numbers
## Part 2: Multiplication
-/

-- Import all the theorems and definitions from Part 1
import Library.Theory.S2.P1

-- Re-open our namespaces
namespace Math301
namespace Nat

-- In this sheet we continue our development of arithmetic by proving some theory about multiplication. To get started we will define the number `one`.

def one : Nat := succ zero

-- The fact that `one` is not equal to `zero` follows from the way inductive types work in Lean. A natural number can either be `zero` or `succ n` for some `n : Nat`, but not both. The tactic `contradiction` helps us use this fact.
theorem one_ne_zero : one ≠ zero := by
  intro h
  contradiction
  done

-- Adding one is the same thing as the successor function.
theorem add_one (a : Nat) : a + one = succ a := by
  rw [one, add_succ, add_zero]
  done

-- Here we define multiplication inductively on the second component similar to how we did for addition.
def mul (a b : Nat) : Nat :=
  match b with
  | Nat.zero => zero
  | Nat.succ c => (mul a c) + a

-- The next line allows us to use the infix notation `a * b` instead of writing `mul a b`.
instance : Mul Nat where
  mul := mul

-- These are true by definition.
theorem mul_zero (a : Nat) : a * zero = zero := by rfl
theorem mul_succ (a b : Nat) : a * succ b = (a * b) + a := by rfl

-- Now some practice for you! Good luck.
theorem zero_mul (a : Nat) : zero * a = zero := by
  induction' a with a ih
  · rfl
  · rw [mul_succ, ih, add_zero]
  done

-- This one took me a lot of `rw` steps.
theorem succ_mul (a b : Nat) : succ a * b = a * b + b := by
  induction' b with b ih
  · rw [mul_zero, mul_zero, add_zero]
  · rw [mul_succ, ih, mul_succ, add_succ, add_succ, add_assoc, add_comm b a, ← add_assoc]
  done

-- Left distributive property
theorem mul_add (a b c : Nat) : a * (b + c) = (a * b) + (a * c) := by
  induction' c with c ih
  · rw [add_zero, mul_zero, add_zero]
  · rw [add_succ, mul_succ, ih, mul_succ, add_assoc]
  done

-- Multiplication is associative.
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction' c with c ih
  · rw [mul_zero, mul_zero, mul_zero]
  · rw [mul_succ, mul_succ, mul_add, ih]
  done

-- Multiplication is commutative.
theorem mul_comm (a b : Nat) : a * b = b * a := by
  induction' b with b ih
  · rw [mul_zero, zero_mul]
  · rw [mul_succ, succ_mul, ih]
  done

-- Right distributivity.
theorem add_mul (a b c : Nat) : (b + c) * a = (b * a) + (c * a) := by
  rw [mul_comm, mul_comm b a, mul_comm c a, mul_add]
  done

-- One is a right identity for multiplication...
theorem mul_one (a : Nat) : a * one = a := by
  rw [one, mul_succ, mul_zero, zero_add]
  done

-- ...and a left identity.
theorem one_mul (a : Nat) : one * a = a := by
  rw [mul_comm, mul_one]
  done

-- Let's define two
def two : Nat := succ one

-- 2a = a + a
theorem two_mul (a : Nat) : two * a = a + a := by
  rw [two, succ_mul, one_mul]
  done

end Nat
end Math301
