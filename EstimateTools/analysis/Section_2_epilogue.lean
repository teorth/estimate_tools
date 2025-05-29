import Mathlib.Tactic
import EstimateTools.analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are isomorphic in various standard senses to the standard natural numbers `ℕ`.


From this point onwards, `Chapter2.Nat` will be deprecated, and we will use the standard natural numbers `ℕ` instead.  In particular, one should use the full Mathlib API for `ℕ` for all subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned transition.

-/

abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | Chapter2.Nat.zero => 0
  | Chapter2.Nat.succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := Chapter2.Nat.toNat
  invFun := fun n ↦ (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn
    . rfl
    simp [Chapter2.Nat.succ_toNat, hn]
    symm
    exact succ_eq_add_one _
  right_inv n := by
    induction' n with n hn
    . rfl
    simp [←succ_eq_add_one]
    exact hn

abbrev Chapter2.Nat.equivNat_order : Chapter2.Nat ≃o ℕ where
  toEquiv := Chapter2.Nat.equivNat
  map_rel_iff' := by
    intro n m
    simp [equivNat]
    sorry

abbrev Chapter2.Nat.equivNat_ring : Chapter2.Nat ≃+* ℕ where
  toEquiv := Chapter2.Nat.equivNat
  map_add' := by
    intro n m
    simp [equivNat]
    sorry
  map_mul' := by
    intro n m
    simp [equivNat]
    sorry

lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) : n.toNat ^ m.toNat = n^m := by
  sorry
