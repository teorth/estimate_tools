import Mathlib.Tactic
import EstimateTools.analysis.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.

I have attempted to make the translation as faithful as possible to the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers). Let m be a natural number. To add zero to m, we define 0 + m := m. Now suppose inductively that we have defined how to add n to m. Then we can add n++ to m by defining (n++) + m := (n + m)++.
-/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

instance Nat.add_inst : Add Nat where
  add := Nat.add

/-- Thus for instance 0 + m = m... -/
theorem zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

theorem succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- 1 + m = (0++) + m = m++ -/
theorem one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

/-- 2 + m = (1++) + m = (m++)++ -/
theorem two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

/-- for instance we have 2 + 3 = (3++)++ = 4++ = 5.-/
example : (2:Nat) + 3 = 5 := by
  rw [two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- Notice that the sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2: For any natural number n, n + 0 = n. -/
lemma add_zero (n:Nat) : n + 0 = n := by
-- We use induction.
  revert n; apply induction
  . -- The base case $0+0=0$ follows since we know that $0+m=m$ for every natural number $m$, and 0 is a natural number.
    exact zero_add 0
  -- Now suppose inductively that $n+0=n$.  We wish to show that $(n++)+0 = n++$.
  intro n ih
  -- But by definition of addition, $(n++)+0$ is equal to $(n+0)++$, which is equal to $n++$ since $n+0 = n$.
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]
  -- This closes the induction.

/-- For any natural numbers $n$ and $m$, $n+(m++) = (n+m)++$. -/
lemma add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- We induct on $n$ (keeping $m$ fixed).
  revert n; apply induction
  . -- We first consider the base case $n=0$.  In this case we have to prove $0+(m++) = (0+m)++$.
    -- But by definition of addition, $0+(m++) = m++$ and $0+m = m$, so both sides are equal to $m++$ and are thus equal to each other.
    rw [zero_add, zero_add]
  -- Now we assume inductively that $n+(m++) = (n+m)++$; we now have to show that $(n++)+(m++) = ((n++)+m)++$.
  intro n ih
  -- The left-hand side is $(n+(m++))++$ by definition of addition, which is equal to $((n+m)++)++$ by the inductive hypothesis.
  rw [succ_add, ih]
  -- Similarly, we have $(n++)+m = (n+m)++$ by the definition of addition, and so the right-hand side is also equal to $((n+m)++)++$.
  rw [succ_add]
  -- Thus both sides are equal to each other, and we have closed the induction.


/-- As a particular corollary of Lemma 2.2.2 and Lemma 2.2.3 we see that n++ = n + 1 (Why?) -/
theorem succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  sorry

/-- Proposition 2.2.4 (Addition is commutative): For any natural numbers $n$ and $m$, $n+m = m+n$. -/
theorem add_comm (n m:Nat) : n + m = m + n := by
  -- We shall use induction on $n$ (keeping $m$ fixed).
  revert n; apply induction
  . -- First we do the base case $n=0$, i.e., we show $0+m = m+0$.
    -- By the definition of addition, $0+m = m$, while by Lemma 2.2.2, $m+0 = m$.  Thus the base case is done.
    rw [zero_add, add_zero]
  -- Now suppose inductively that $n+m=m+n$, now we have to prove that $(n++)+m = m+(n++)$ to close the induction.
  intro n ih
  -- By the definition of addition, $(n++)+m = (n+m)++$.
  rw [succ_add]
  -- By Lemma 2.2.3, $m+(n++) = (m+n)++$, but this is equal to $(n+m)++$ by the inductive hypothesis $n+m=m+n$.
  rw [add_succ, ih]
  -- Thus $(n++)+m = m+(n++)$ and we have closed the induction.

/-- Proposition 2.2.5 (Addition is associative). For any natural numbers a, b, c, we have (a + b) + c = a + (b + c).-/
theorem add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  sorry

/-- Proposition 2.2.6 (Cancellation law). Let a, b, c be natural numbers such that a + b = a + c. Then we have b = c.-/
theorem add_cancel_left (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- We prove this by induction on $a$.
  revert a; apply induction
  . -- First consider the base case $a=0$.  Then we have $0+b=0+c$,
    intro hbc
    -- which by definition of addition implies that $b=c$ as desired.
    rwa [zero_add, zero_add] at hbc
  -- Now suppose inductively that we have the cancellation law for $a$ (so that $a+b=a+c$ implies $b=c$); we now have to prove the cancellation law for $a++$.
  intro a ih
  -- In other words, we assume that $(a++)+b = (a++)+c$ and need to show that $b=c$.
  intro hbc
  -- By the definition of addition, $(a++)+b=(a+b)++$ and $(a++)+c=(a+c)++$ and so we have $(a+b)++ = (a+c)++$.
  rw [succ_add, succ_add] at hbc
  -- By Axiom 2.4, we have $a+b=a+c$.
  replace hbc := succ_cancel hbc
  --  Since we already have the cancellation law for $a$, we thus have $b=c$ as desired.
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers). A natural number n is said to be positive iff it is not equal to 0.-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8. If a is a positive natural number, and b is a natural number, then a + b is positive (and hence b + a is also, by Proposition 2.2.4).-/
theorem pos_add {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  --  We use induction on $b$.
  revert b; apply induction
  . -- If $b=0$, then $a+b = a+0 = a$, which is positive, so this proves the base case.
    rwa [add_zero]
  -- Now suppose inductively that $a+b$ is positive.
  intro b hab
  -- Then $a+(b++) = (a+b)++$,
  rw [add_succ]
  -- which cannot be zero by Axiom 2.3, and is hence positive.
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this
  -- This closes the induction.

theorem add_pos {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact pos_add _ ha

/-- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0, then a = 0 and b = 0.-/
theorem add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- Suppose for sake of contradiction
  by_contra h
  -- that a ̸= 0 or b ̸= 0.
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . -- If a ̸= 0 then a is positive
    rw [← Nat.isPos_iff] at ha
    -- and hence a+b = 0 is positive by Proposition 2.2.8,
    have : (a + b).isPos := pos_add _ ha
    -- a contradiction.
    contradiction
  -- Similarly if b ̸= 0 then b is positive
  rw [← Nat.isPos_iff] at hb
  -- and again a+b = 0 is positive by Proposition 2.2.8,
  have : (a + b).isPos := add_pos _ hb
  -- a contradiction.
  contradiction

/-- Lemma 2.2.10. Let a be a positive number. Then there exists exactly one natural number b such that b++ = a.-/
lemma uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  sorry

/-- Definition 2.2.11 (Ordering of the natural numbers). Let n and m be natural numbers. We say that n is greater than or equal to m, and write n ≥ m or m ≤ n, iff we have n = m + a for some natural number a. We say that n is strictly greater than m, and write n > m or m < n, iff n ≥ m and n ̸= m. -/

instance Nat.LE_inst : LE Nat where
  le := fun n m ↦ ∃ a:Nat, m = n + a

instance Nat.LT_inst : LT Nat where
  lt := fun n m ↦ (∃ a:Nat, m = n + a) ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  sorry

/-- Thus for instance 8 > 5, because 8 = 5+3 and 8 ̸= 5. -/
example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Also note that n++ > n for any n -/
theorem Nat.succ_gt (n:Nat) : n++ > n := by
  sorry

/-- Proposition 2.2.12 (Basic properties of order for natural numbers). Let a, b, c be natural numbers. Then
(a) (Order is reflexive) a ≥ a. -/
theorem ge_refl (a:Nat) : a ≥ a := by
  sorry

/-- (b) (Order is transitive) If a ≥ b and b ≥ c, then a ≥ c. -/
theorem ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  sorry

/-- (c) (Order is anti-symmetric) If a ≥ b and b ≥ a, then a = b. -/
theorem ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  sorry

/-- (d) (Addition preserves order) a ≥ b if and only if a + c ≥ b + c. -/
theorem add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  sorry

theorem add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

theorem add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

theorem add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b if and only if a++ ≤ b. -/
theorem lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  sorry

/-- (f) a < b if and only if b = a + d for some positive number d. -/
theorem lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  sorry

/-- If a < b then a ̸= b by definition,-/
theorem ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- and if a > b then a ̸= b by definition. -/
theorem ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then by Proposition 2.2.12 we have a = b, a contradiction -/
theorem not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction



/-- Proposition 2.2.13 (Trichotomy of order for natural numbers). Let a and b be natural numbers. Then exactly one of the following statements is true: a < b, a = b, or a > b.-/
theorem trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- We keep b fixed and induct on a.
  revert a; apply induction
  . -- When a = 0 we have 0 ≤ b for all b (why?),
    have why : 0 ≤ b := by
      sorry
    --  so we have either 0 = b or 0 < b,
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    -- which proves the base case.
    tauto
  -- Now suppose we have proven the proposition for a, and now we prove the proposition for a++.
  intro a ih
  -- From the trichotomy for $a$, there are three cases: $a < b$, $a=b$, and $a>b$.
  rcases ih with case1 | case2 | case3
  . -- suppose that $a < b$.  Then by Proposition 2.2.12, we have $a++ \leq b$.
    rw [lt_iff_succ_le] at case1
    -- Thus either $a\pp = b$ or $a\pp < b$
    rw [Nat.le_iff_lt_or_eq] at case1
    -- and in either case we are done.
    tauto
  . -- If $a=b$, then $a++ > b$ (why?).
    have why : a++ > b := by sorry
    tauto
  -- If $a>b$, then $a++ > b$ (why?)
  have why : a++ > b := by sorry
  tauto
  -- This closes the induction.

/-- (Not from textbook) The order is decidable.  This exercise is only recommended for Lean experts. -/
instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := by
  sorry

/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans := fun a b c hab hbc ↦ ge_trans hbc hab
  lt_iff_le_not_le := sorry
  le_antisymm := fun a b hab hba ↦ ge_antisymm hba hab
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction). Let m₀ be a natural number, and let P(m) be a property pertaining to an arbitrary natural number m. Suppose that for each m ≥ m₀, we have the following implication:
if P(m') is true for all natural numbers m₀ ≤ m' < m, then
P(m) is also true.  Then we can conclude that P(m)
is true for all natural numbers m ≥ m₀.
-/
theorem strong_induction {m₀:Nat} {P: Nat → Prop} (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) : ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Exercise 2.2.6. Let n be a natural number, and let P(m) be a property pertaining to the natural numbers such that whenever P(m++) is true, then P(m) is true. Suppose that P(n) is also true. Prove that P(m) is true for all natural
numbers m ≤ n-/
theorem backwards_induction {n:Nat} {P: Nat → Prop}  (hind: ∀ m, P (m++) → P m) (hn: P n) : ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7. Let n be a natural number, and let P(m) be a property pertaining
to the natural numbers such that whenever P(m) is true, P(m++) is true. Show that if P(n) is true, then P(m) is true for all m ≥ n.-/
theorem induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) : P n → ∀ m, m ≥ n → P m := by
  sorry



end Chapter2
