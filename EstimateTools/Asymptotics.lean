import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import EstimateTools.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Class of functions on a parameter space Ω equipped with a filter that are eventually positive.

class EventuallyPositive {Ω:Type*} (f: Filter Ω) where
  val : Ω → ℝ
  pos : ∀ᶠ N in f, val N > 0

def EventuallyPositive.fn {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : Ω → ℝ := X.val

lemma EventuallyPositive.val_eq {Ω:Type*} {f: Filter Ω} {X Y : EventuallyPositive f} (heq : X.fn = Y.fn) : X = Y := by
  cases X; cases Y
  congr

instance EventuallyPositive.funlike {Ω:Type*} {f: Filter Ω} : FunLike (EventuallyPositive f) Ω ℝ where
  coe := EventuallyPositive.fn
  coe_injective' := fun _ _ heq => EventuallyPositive.val_eq heq

instance EventuallyPositive.LE {Ω:Type*} (f: Filter Ω) : LE (EventuallyPositive f) :=
{
  le := fun X Y => ∃ C > 0, ∀ᶠ N in f, X N ≤ C * Y N
}

def EventuallyPositive.le_iff {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : X ≤ Y ↔ ∃ C > 0, ∀ᶠ N in f, X N ≤ C * Y N := by
 simp; rfl

instance EventuallyPositive.lesssim {Ω:Type*} (f: Filter Ω) : Preorder (EventuallyPositive f) :=
{
  le_refl := by
    intro X; use 1
    simp
  le_trans := by
    intro X Y Z ⟨ C1, hC1, h1 ⟩ ⟨ C2, hC2, h2 ⟩
    use C1 * C2
    refine ⟨ Left.mul_pos hC1 hC2, ?_ ⟩
    filter_upwards [h1, h2, Y.pos] with N h1 h2 this
    calc
      _ ≤ C1 * Y N := h1
      _ ≤ C1 * (C2 * Z N) := by gcongr
      _ = (C1 * C2) * Z N := by rw [mul_assoc]

  lt := fun X Y => (X ≤ Y) ∧ ¬ (Y ≤ X)
  lt_iff_le_not_le := by
    intro X Y
    rfl
}

lemma EventuallyPositive.asymp_iff {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : X ≈ Y ↔ ∃ C, C > 0 ∧ ∀ᶠ N in f, X N ≤ C * (Y N) ∧ Y N ≤ C * (X N) := by
  simp [Preorder.equiv_iff, EventuallyPositive.le_iff]
  constructor
  . intro ⟨ ⟨ C1, hC1, h1 ⟩, ⟨ C2, hC2, h2 ⟩ ⟩
    use max C1 C2
    have hC1_max := le_max_left C1 C2
    have hC2_max := le_max_right C1 C2
    refine ⟨ lt_of_lt_of_le hC1 hC1_max, ?_, ?_ ⟩
    . filter_upwards [h1, h2, Y.pos] with N hX hY hpos
      apply hX.trans
      gcongr
    filter_upwards [h1, h2, X.pos] with N hX hY hpos
    apply hY.trans
    gcongr
  . intro ⟨ C, hC, ⟨ h1, h2 ⟩ ⟩
    refine ⟨ ⟨ C, hC, ?_⟩, ⟨ C, hC, ?_⟩ ⟩
    all_goals filter_upwards [h1,h2] with N hX hY
    . exact hX
    exact hY

instance EventuallyPositive.add {Ω:Type*} (f: Filter Ω) : Add (EventuallyPositive f) :=
{
  add := fun X Y => {
    val := X.fn + Y.fn
    pos := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact Right.add_pos' h1 h2
  }
}

@[simp]
lemma EventuallyPositive.add_val {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : (X + Y).fn = X.fn + Y.fn := rfl


instance EventuallyPositive.mul {Ω:Type*} (f: Filter Ω) : Mul (EventuallyPositive f) :=
{
  mul := fun X Y => {
  val := X.fn * Y.fn
  pos := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact Left.mul_pos h1 h2
  }
}

@[simp]
lemma EventuallyPositive.mul_val {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : (X * Y).fn = X.fn * Y.fn := rfl

noncomputable instance EventuallyPositive.div {Ω:Type*} (f: Filter Ω) : Div (EventuallyPositive f) :=
{
  div := fun X Y => {
    val := X.fn / Y.fn
    pos := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact div_pos h1 h2
  }
}

instance EventuallyPositive.addCommSemigroup {Ω:Type*} (f: Filter Ω) : AddCommSemigroup (EventuallyPositive f) :=
{
  add_assoc := by
    intro X Y Z
    apply EventuallyPositive.val_eq
    simp [add_assoc]
  add_comm := by
    intro X Y
    apply EventuallyPositive.val_eq
    simp [add_comm]
}

instance EventuallyPositive.one {Ω:Type*} (f: Filter Ω) : One (EventuallyPositive f) :=
{
  one := {
    val := fun _ => 1
    pos := by
      filter_upwards [f.univ_mem] with N _
      exact zero_lt_one
  }
}

@[simp]
lemma EventuallyPositive.one_val {Ω:Type*} {f: Filter Ω} : (1 : EventuallyPositive f).fn = 1 := rfl

instance EventuallyPositive.monoid {Ω:Type*} (f: Filter Ω) : CommMonoid (EventuallyPositive f) :=
{
  mul_assoc := by
    intro X Y Z
    apply EventuallyPositive.val_eq
    simp [mul_assoc]
  mul_comm := by
    intro X Y
    apply EventuallyPositive.val_eq
    simp [mul_comm]
  one_mul := by
    intro X
    apply EventuallyPositive.val_eq
    simp [one_mul]
  mul_one := by
    intro X
    apply EventuallyPositive.val_eq
    simp [mul_one]
}

instance EventuallyPositive.distrib {Ω:Type*} (f: Filter Ω) : Distrib (EventuallyPositive f) :=
{
  left_distrib := by
    intro X Y Z
    apply EventuallyPositive.val_eq
    simp [mul_add]
  right_distrib := by
    intro X Y Z
    apply EventuallyPositive.val_eq
    simp [add_mul]
}

noncomputable instance EventuallyPositive.pow {Ω:Type*} (f: Filter Ω) : Pow (EventuallyPositive f) ℝ :=
{
  pow := fun X α => {
    val := fun N => X N ^ α
    pos := by
      filter_upwards [X.pos] with N hN
      exact Real.rpow_pos_of_pos hN α
  }
}

@[simp]
lemma EventuallyPositive.rpow_val {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (α:ℝ) : (X ^ α).fn = X.fn ^ α := rfl

@[simp]
lemma EventuallyPositive.pow_val {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (n:ℕ) : (X ^ n).fn = X.fn ^ n := by
  induction' n with n hn
  . simp
  ext N
  simp [pow_add, hn]

lemma EventuallyPositive.rpow_eq_pow {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (n:ℕ) : X ^ (n:ℝ) = X ^ n := by
  apply EventuallyPositive.val_eq
  ext N
  simp [EventuallyPositive.rpow_val, EventuallyPositive.pow_val]


def OrderOfMagnitude {Ω:Type*} (f: Filter Ω) := OrderQuotient (EventuallyPositive f)

def EventuallyPositive.order {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : OrderOfMagnitude f :=
  Quot.mk (Preorder.toSetoid) X

def EventuallyPositive.order_eq_iff {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : X.order = Y.order ↔ X ≈ Y := by
  exact OrderQuotient.quot_eq_iff X Y

instance OrderOfMagnitude.add {Ω:Type*} (f: Filter Ω) : Add (OrderOfMagnitude f) :=
{
  add := Quotient.lift₂ (fun X Y ↦ (X + Y).order) (by
    intro X₁ Y₁ X₂ Y₂ hX hY
    simp
    rw [EventuallyPositive.order_eq_iff]
    sorry
  )

}
