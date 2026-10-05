import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1

This file is a translation of Section 4.1 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of  the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a — b` of natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- addition, multiplication, and negation of these integers, as well as an embedding of ℕ

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Exercise 4.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r := fun a b ↦ a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      have h3 := congrArg₂ (· + ·) h1 h2
      simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " — " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a — b = c — d ↔ a + d = c + b := by
  constructor
  . exact Quotient.exact
  intro h; exact Quotient.sound h

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a — b := by
  apply Quot.ind _ n; intro ⟨ a, b ⟩
  use a, b; rfl

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.add_inst : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) — (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a — b = a' — b') : (a*c+b*d) — (a*d+b*c) = (a'*c+b'*d) — (a'*d+b'*c) := by
  simp only [Int.eq] at h ⊢
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c — d = c' — d') : (a*c+b*d) — (a*d+b*c) = (a*c'+b*d') — (a*d'+b*c') := by
  simp only [Int.eq] at h ⊢
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a — b = a' — b') (h2: c — d = c' — d') :
  (a*c+b*d) — (a*d+b*c) = (a'*c'+b'*d') — (a'*d'+b'*c') := by
  rw [Int.mul_congr_left a b a' b' c d h1, Int.mul_congr_right a' b' c d c' d' h2]

instance Int.mul_inst : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) — (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp at h1 h2
    convert Int.mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a — b * c — d = (a*c+b*d) — (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.ofnat_inst {n:ℕ} : OfNat Int n where
  ofNat := n — 0

instance Int.natCast_inst : NatCast Int where
  natCast n := n — 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n — 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n — 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
      simp only [Int.ofNat_eq, Int.eq, add_zero]
      rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) :
    (n : Int) = (m : Int) ↔ n = m := by
      simp only [Int.natCast_eq, Int.eq, add_zero]

example : 3 = 3 — 0 := by rfl

example : 3 = 4 — 1 := by
  rw [Int.ofNat_eq, Int.eq]

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.neg_inst : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b — a) (by
    sorry)

theorem Int.neg_eq (a b:ℕ) : -(a — b) = b — a := rfl

example : -(3 — 5) = 5 — 3 := by rfl

abbrev Int.isPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.isNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := Int.eq_diff x
  have := _root_.trichotomous (r := LT.lt) a b
  rcases this with h_lt | h_eq | h_gt
  . obtain ⟨ c,rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, ?_, ?_ ⟩
    . linarith
    simp_rw [Int.natCast_eq, Int.neg_eq, Int.eq]
    abel
  . left; simp_rw [h_eq, Int.ofNat_eq, Int.eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, ?_, ?_ ⟩
  . linarith
  simp_rw [Int.natCast_eq, Int.eq]
  abel

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.isPos → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩
  simp [←Int.natCast_ofNat] at hn'
  linarith

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.isNeg → False := by
  rintro ⟨ rfl, ⟨ n, hn, hn' ⟩ ⟩
  simp_rw [←Int.natCast_ofNat, Int.natCast_eq, Int.neg_eq, Int.eq] at hn'
  linarith

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.not_pos_neg (x:Int) : x.isPos ∧ x.isNeg → False := by
  rintro ⟨ ⟨ n, hn, rfl ⟩, ⟨ m, hm, hm' ⟩ ⟩
  simp_rw [Int.natCast_eq,Int.neg_eq, Int.eq] at hm'
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.addGroup_inst : AddGroup Int :=
AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.monoid_inst : Monoid Int where
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := Int.eq_diff x
    obtain ⟨ c, d, rfl ⟩ := Int.eq_diff y
    obtain ⟨ e, f, rfl ⟩ := Int.eq_diff z
    simp_rw [Int.mul_eq]
    congr 1
    . ring
    ring
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.commRing_inst : CommRing Int where
  add_comm := by sorry
  mul_comm := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a — b := by sorry

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by sorry

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by sorry

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.LE_inst : LE Int where
  le := fun n m ↦ ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.LT_inst : LT Int where
  lt := fun n m ↦ (∃ a:ℕ, m = n + a) ∧ n ≠ m

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.gt_iff (a b:Int) : a > b ↔ ∃ n:ℕ, n ≠ 0 ∧ a = b + n := by sorry

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_gt_add_right {a b:Int} (c:Int) (h: a > b) : a+c > b+c := by sorry

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_left {a b c:Int} (hab : a > b) (hc: c > 0) : a*c > b*c := by sorry

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: a > b) : -a < -b := by sorry

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.gt_trans {a b c:Int} (hab: a > b) (hbc: b > c) : a > c := by sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b c:Int) : a > b ∨ a < b ∨ a = b := by sorry

private lemma Int.add_nat (a b k:ℕ) : a — b + k = (a + k) — b := rfl

private lemma Int.add_zero_nat (b:Int) : b + (0:ℕ) = b := by
  obtain ⟨x, y, rfl⟩ := Int.eq_diff b
  rw [Int.add_nat]; rfl

private lemma Int.add_natCast_eq (a b k:ℕ) : a — b + (k:Int) = (a + k) — b := by
  show a — b + (k — 0) = (a + k) — b
  rfl

private lemma Int.add_add_natCast_repr (a c p q:ℕ) :
    ((a — c) + p) + q = (a — c) + (p + q) := by
  have h1 : (a — c) + p = (a + p) — c := Int.add_nat a c p
  have h2 : ((a + p) — c) + q = (a + p + q) — c := Int.add_nat (a + p) c q
  have h3 : (a — c) + (p + q) = (a + (p + q)) — c := Int.add_nat a c (p + q)
  calc ((a — c) + p) + q = (a + p) — c + q := by rw [h1]
    _ = (a + p + q) — c := h2
    _ = (a + (p + q)) — c := by rw [Nat.add_assoc]
    _ = (a — c) + (p + q) := by rw [← h3]

private lemma Int.add_add_natCast (b:Int) (p q:ℕ) : (b + p) + q = b + (p + q) := by
  obtain ⟨a, c, rfl⟩ := Int.eq_diff b
  exact Int.add_add_natCast_repr a c p q

private lemma Int.add_natCast_right_cancel {n:Int} {k:ℕ} (h : n = n + k) : k = 0 := by
  obtain ⟨a, b, rfl⟩ := Int.eq_diff n
  have heq : (a + k) — b = a — b := by
    rw [← Int.add_nat]
    exact h.symm
  have hsum : a + k = a := Nat.add_right_cancel ((Int.eq (a + k) b a b).mp heq)
  omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  rintro ⟨hgt, hlt⟩
  simp only [gt_iff_lt, Int.LT_inst] at hgt hlt
  rcases hgt with ⟨⟨p, hp⟩, hbne⟩
  rcases hlt with ⟨⟨q, hq⟩, _⟩
  have hpq : p + q = 0 := by
    have h : b = b + (p + q) := by
      calc b = a + q := hq
        _ = (b + p) + q := by rw [← hp]
        _ = b + (p + q) := Int.add_add_natCast b p q
    exact Int.add_natCast_right_cancel h
  have hp0 : p = 0 := (Nat.add_eq_zero.mp hpq).1
  have hp' : a = b + (0:ℕ) := by simpa [hp0] using hp
  have : a = b := hp'.trans (Int.add_zero_nat b)
  exact hbne this.symm

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  rintro ⟨hgt, heq⟩
  subst heq
  simp only [gt_iff_lt, Int.LT_inst] at hgt
  exact hgt.2 rfl

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  rintro ⟨hlt, heq⟩
  subst heq
  simp only [Int.LT_inst] at hlt
  exact hlt.2 rfl

/-- (Not from textbook) The order is decidable.  This exercise is only recommended for Lean experts. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  sorry

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.linearOrder : LinearOrder Int where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by sorry

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, P 0 ∧ ∀ n, P n → P (n+1) ∧ ¬ ∀ n, P n := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg (n:Int) : n*n ≥ 0 := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by sorry

/-- Not in textbook: create an equivalence between Int and ℤ.  This requires some familiarity with the API for Mathlib's version of the integers. -/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := sorry
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Int.equivInt_order : Int ≃o ℤ where
  toEquiv := Int.equivInt
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Int.equivInt_ring : Int ≃+* ℤ where
  toEquiv := Int.equivInt
  map_add' := by sorry
  map_mul' := by sorry

end Section_4_1
