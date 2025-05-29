import Init.Prelude
import Mathlib.Tactic

namespace Chapter2

/-- Assumption 2.6: There exists a number system N, whose elements we call natural numbers, for which the Peano axioms 2.1-2-5 are true.

This system is ultimately isomorphic to _root_.Nat, but for this section we build up the properties of this class "by hand".
 -/
inductive Nat where
| zero : Nat
| succ : Nat → Nat

/-- Axiom 2.1: 0 is a natural number. -/
instance Nat.zero_inst : Zero Nat := ⟨ Nat.zero ⟩
#check (0:Nat)

/- Axiom 2.2: Successor of a natural number is a natural number. -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)


/-- Definition 2.1.3: We define 1 to be the number 0++, 2 to be the number (0++)++, etc. Note: to avoid ambiguity, one may need to use explicit casts such as (0:Nat), (1:Nat), etc. to refer to this Chapter's version of the natural numbers. -/
instance Nat.ofnat_inst {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ ↦ Nat.succ) n

instance Nat.one_inst : One Nat := ⟨ 1 ⟩
theorem succ_zero_eq_one : 0++ = 1 := by
  rfl
#check (1:Nat)

theorem succ_one_eq_two : 1++ = 2 := by
  rfl
#check (2:Nat)

/-- Proposition 2.1.4: 3 is a natural number.-/
theorem succ_two_eq_three : 2++ = 3 := by
  rfl
#check (3:Nat)

/-- Axiom 2.3: 0 is not the successor of any natural number. -/
theorem axiom_2_3 (n:Nat) : n.succ ≠ 0 := by
  by_contra h
  simp only [reduceCtorEq] at h

/-- Proposition 2.1.6: 4 is not equal to zero. -/
theorem prop_2_1_6 : (4:Nat) ≠ 0 := by
  -- By definition, 4 = 3++.
  change 3++ ≠ 0
  -- By axiom 2.3, 3++ is not zero.
  exact axiom_2_3 _

/-- Axiom 2.4: Different natural numbers must have different successors. -/
theorem axiom_2_4' {n m:Nat} (hnm: n++ = m++) : n = m := by
  rwa [Nat.succ.injEq] at hnm

theorem axiom_2_4 (n m:Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose! h
  exact axiom_2_4' h

/-- Proposition 2.1.8: 6 is not equal to 2. -/
theorem prop_2_1_8 : (6:Nat) ≠ 2 := by
-- Suppose for sake of conradiction that 6 = 2.
  by_contra h
-- Then 5++ = 1++
  change 5++ = 1++ at h
--  , so by Axiom 2.4 we have 5 = 1,
  replace h := axiom_2_4' h
-- so that 4++ = 0++
  change 4++ = 0++ at h
-- , so that 4 = 0.
  replace h := axiom_2_4' h
-- which contradicts our previous proposition.
  have := prop_2_1_6
  contradiction

/-- Axiom 2.5 (principle of mathematical induction)  Let P(n) be any property pertaining to a natural number n.  Suppose that P(0) is true, and suppose that whenever P(n) is true, P(n++) is true.  Then P(n) is true for every natural number n. -/
theorem axiom_2_5 (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (Nat.recurse f c n)

/-- Proposition 2.1.16 (recursive definitions) Suppose for each natural number n, we have some function f_n: N → N from the natural numbers to the natural numbers.  Then we can assign a unique natural number a_n to each natural number n, such that a_0 = c and a_{n++} = f_n(a_n) for all n. -/
theorem prop_2_1_16_a (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl

theorem prop_2_1_16_b (f: Nat → Nat → Nat) (c: Nat) (n: Nat) : Nat.recurse f c (n++) = f n (Nat.recurse f c n) := by rfl

theorem prop_2_1_16_c (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) : (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = Nat.recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    apply funext
    -- We use induction.
    apply axiom_2_5
    . -- We first observe that this procedure gives a single value to a_0, namely c.
      exact h0
    -- Now suppose inductively that the proposition gives a single value to a_n.
    intro n hn
    -- Then it gives a single value to a_{n++}, namely f_n(a_n).
    rw [hsucc n, prop_2_1_16_b, hn]
  intro h
  rw [h]
  constructor
  . exact prop_2_1_16_a _ _
  exact prop_2_1_16_b _ _

theorem prop_2_1_16_d (f: Nat → Nat → Nat) (c: Nat) : ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
apply ExistsUnique.intro (Nat.recurse f c)
. constructor
  . exact prop_2_1_16_a _ _
  . exact prop_2_1_16_b _ _
intro a
exact (prop_2_1_16_c _ _ a).mp

end Chapter2
