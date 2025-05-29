import Mathlib.Tactic
import EstimateTools.analysis.Section_2_2

/-!
# Analysis I, Section 2.3

This file is a translation of Section 2.3 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of  the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers, `Chapter2.Nat`

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.mul_inst : Mul Nat where
  mul := Nat.mul

theorem zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

theorem succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

theorem one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- Lemma 2.3.2 (Multiplication is commutative)-/
lemma mul_comm (n m: Nat) : n * m = m * n := by
  sorry

theorem mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

lemma mul_zero (n: Nat) : n * 0 = 0 := by
  rw [mul_comm, zero_mul]

lemma mul_succ (n m:Nat) : n * m++ = n * m + n := by
  rw [mul_comm, succ_mul, mul_comm]

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) -/
lemma mul_eq_zero_iff (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  sorry

lemma pos_mul_pos {n m: Nat} (h₁: n.isPos) (h₂: m.isPos) : (n * m).isPos := by
  sorry

/-- Proposition 2.3.4 (Distributive law)-/
theorem mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

theorem add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) -/
theorem mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  sorry

/-- (Not from textbook)  Nat is a commutative semiring. -/
instance Nat.commSemiring_inst : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.isPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  apply_fun (· * c) at hd
  rw [add_mul] at hd
  have hdcpos : (d * c).isPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

theorem mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.isPos) : a * c > b * c := mul_lt_mul_of_pos_right h hc

theorem mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.isPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

theorem mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.isPos) : c * a > c * b := mul_lt_mul_of_pos_left h hc



/-- Corollary 2.3.7 (Cancellation law) -/
lemma mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.isPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

/-- (Not from textbook) Nat is an ordered semiring. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by sorry
  mul_le_mul_of_nonneg_left := by sorry
  mul_le_mul_of_nonneg_right := by sorry


/-- Proposition 2.3.9 (Euclid's division lemma)-/
theorem exists_div_mod (n :Nat) {q: Nat} (hq: q.isPos) : ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.pow_inst : HomogeneousPow Nat where
  pow := Nat.pow

theorem zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

theorem zero_pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m := recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Exercise 2.3.4-/
theorem sq_add_eq (a b: Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry




end Chapter2
