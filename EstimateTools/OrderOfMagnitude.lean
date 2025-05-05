import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import EstimateTools.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Class of functions on a parameter space Ω equipped with a filter that are eventually positive.

class EventuallyPositive {Ω:Type*} (f: Filter Ω) where
  val : Ω → ℝ
  positive : ∀ᶠ N in f, val N > 0

def EventuallyPositive.fn {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : Ω → ℝ := X.val

lemma EventuallyPositive.val_eq {Ω:Type*} {f: Filter Ω} {X Y : EventuallyPositive f} (heq : X.fn = Y.fn) : X = Y := by
  cases X; cases Y
  congr

instance EventuallyPositive.funlike {Ω:Type*} {f: Filter Ω} : FunLike (EventuallyPositive f) Ω ℝ where
  coe := EventuallyPositive.fn
  coe_injective' := fun _ _ heq => EventuallyPositive.val_eq heq

def EventuallyPositive.pos {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : ∀ᶠ N in f, X N > 0 := X.positive

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

lemma EventuallyPositive.asymp_of_eventual_eq {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) (h : ∀ᶠ N in f, X N = Y N) : X ≈ Y := by
  rw [EventuallyPositive.asymp_iff]
  refine ⟨ 1, Real.zero_lt_one, ?_ ⟩
  filter_upwards [h] with N hN
  simp [hN]

instance EventuallyPositive.add {Ω:Type*} (f: Filter Ω) : Add (EventuallyPositive f) :=
{
  add := fun X Y => {
    val := X.fn + Y.fn
    positive := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact Right.add_pos' h1 h2
  }
}

@[simp]
lemma EventuallyPositive.add_val {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : (X + Y).fn = X.fn + Y.fn := rfl

@[simp]
lemma EventuallyPositive.add_eval {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) (N:Ω) : (X + Y) N = X N + Y N := rfl



instance EventuallyPositive.mul {Ω:Type*} (f: Filter Ω) : Mul (EventuallyPositive f) :=
{
  mul := fun X Y => {
  val := X.fn * Y.fn
  positive := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact Left.mul_pos h1 h2
  }
}

@[simp]
lemma EventuallyPositive.mul_val {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : (X * Y).fn = X.fn * Y.fn := rfl

@[simp]
lemma EventuallyPositive.mul_eval {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) (N:Ω) : (X * Y) N = X N * Y N := rfl

noncomputable instance EventuallyPositive.inv {Ω:Type*} (f: Filter Ω) : Inv (EventuallyPositive f) :=
{
  inv := fun X => {
    val := fun N => 1 / X N
    positive := by
      filter_upwards [X.pos] with N hN
      exact one_div_pos.mpr hN
  }
}

@[simp]
lemma EventuallyPositive.inv_val {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) : (X⁻¹).fn = 1 / X.fn := rfl

@[simp]
lemma EventuallyPositive.inv_eval {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (N:Ω) : (X⁻¹) N = 1 / X N := rfl

noncomputable instance EventuallyPositive.div {Ω:Type*} (f: Filter Ω) : Div (EventuallyPositive f) :=
{
  div := fun X Y => {
    val := X.fn / Y.fn
    positive := by
      filter_upwards [X.pos, Y.pos] with N h1 h2
      exact div_pos h1 h2
  }
}

@[simp]
lemma EventuallyPositive.div_val {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) : (X / Y).fn = X.fn / Y.fn := rfl

@[simp]
lemma EventuallyPositive.div_eval {Ω:Type*} {f: Filter Ω} (X Y : EventuallyPositive f) (N:Ω) : (X / Y) N = X N / Y N := rfl

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
    positive := by
      filter_upwards [f.univ_mem] with N _
      exact zero_lt_one
  }
}

@[simp]
lemma EventuallyPositive.one_val {Ω:Type*} {f: Filter Ω} : (1 : EventuallyPositive f).fn = 1 := rfl

@[simp]
lemma EventuallyPositive.one_eval {Ω:Type*} {f: Filter Ω} (N:Ω) : (1 : EventuallyPositive f) N = 1 := rfl

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
    positive := by
      filter_upwards [X.pos] with N hN
      exact Real.rpow_pos_of_pos hN α
  }
}

@[simp]
lemma EventuallyPositive.rpow_val {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (α:ℝ) : (X ^ α).fn = X.fn ^ α := rfl

@[simp]
lemma EventuallyPositive.rpow_eval {Ω:Type*} {f: Filter Ω} (X : EventuallyPositive f) (N:Ω) (α:ℝ) : (X ^ α) N = X N ^ α := rfl

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




abbrev OrderOfMagnitude {Ω:Type*} (f: Filter Ω) := OrderQuotient (EventuallyPositive f)

abbrev EventuallyPositive.order {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : OrderOfMagnitude f :=
  Preorder.quotient X

def EventuallyPositive.order_eq_iff {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : X.order = Y.order ↔ X ≈ Y := by
  exact OrderQuotient.quot_eq_iff X Y

def OrderOfMagnitude.ind {Ω:Type*} {f: Filter Ω} {β : OrderOfMagnitude f → Prop} (mk : ∀ (X : EventuallyPositive f), β X.order) (X : OrderOfMagnitude f) : β X := Quot.ind mk X


def EventuallyPositive.order_le {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : X.order ≤ Y.order ↔ X ≤ Y := OrderQuotient.quot_le_iff X Y


instance OrderOfMagnitude.add {Ω:Type*} (f: Filter Ω) : Add (OrderOfMagnitude f) :=
{
  add := Quotient.lift₂ (fun X Y ↦ (X + Y).order) (by
    intro X₁ Y₁ X₂ Y₂ hX hY
    simp
    rw [EventuallyPositive.order_eq_iff]
    simp [EventuallyPositive.asymp_iff] at hX hY ⊢
    obtain ⟨ CX, ⟨ hCX, hX₁, hX₂ ⟩ ⟩ := hX
    obtain ⟨ CY, ⟨ hCY, hY₁, hY₂ ⟩ ⟩ := hY
    use max CX CY
    have hCX_max := le_max_left CX CY
    have hCY_max := le_max_right CX CY
    refine ⟨ lt_of_lt_of_le hCX hCX_max, ?_, ?_ ⟩
    . filter_upwards [hX₁, hY₁, X₂.pos, Y₂.pos] with N hX hY hXpos hYpos
      calc
        _ ≤ CX * X₂ N + CY * Y₂ N := by gcongr
        _ ≤ (max CX CY) * X₂ N + (max CX CY) * Y₂ N := by gcongr
        _ = (max CX CY) * (X₂ N + Y₂ N) := by rw [mul_add]
    filter_upwards [hX₂, hY₂, X₁.pos, Y₁.pos] with N hX hY hXpos hYpos
    calc
      _ ≤ CX * X₁ N + CY * Y₁ N := by gcongr
      _ ≤ (max CX CY) * X₁ N + (max CX CY) * Y₁ N := by gcongr
      _ = (max CX CY) * (X₁ N + Y₁ N) := by rw [mul_add]
  )
}

def EventuallyPositive.order_add {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : (X + Y).order = X.order + Y.order := by
  apply Quotient.sound
  simp [EventuallyPositive.asymp_iff]

instance OrderOfMagnitude.addCommSemigroup {Ω:Type*} (f: Filter Ω) : AddCommSemigroup (OrderOfMagnitude f) :=
{
  add_assoc := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    apply OrderOfMagnitude.ind; intro Z
    simp only [←EventuallyPositive.order_add, add_assoc]
  add_comm := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    simp only [←EventuallyPositive.order_add, add_comm]
}

instance OrderOfMagnitude.mul {Ω:Type*} (f: Filter Ω) : Mul (OrderOfMagnitude f) :=
{
  mul := Quotient.lift₂ (fun X Y ↦ (X * Y).order) (by
    intro X₁ Y₁ X₂ Y₂ hX hY
    simp
    rw [EventuallyPositive.order_eq_iff]
    simp [EventuallyPositive.asymp_iff] at hX hY ⊢
    obtain ⟨ CX, ⟨ hCX, hX₁, hX₂ ⟩ ⟩ := hX
    obtain ⟨ CY, ⟨ hCY, hY₁, hY₂ ⟩ ⟩ := hY
    use CX * CY
    refine ⟨ mul_pos hCX hCY, ?_, ?_ ⟩
    . filter_upwards [hX₁, hY₁, X₁.pos, X₂.pos, Y₁.pos, Y₂.pos] with N hX hY hX₁pos hX₂pos hY₁pos hY₂pos
      calc
        _ ≤ (CX * X₂ N) * (CY * Y₂ N) := by gcongr
        _ = (CX * CY) * (X₂ N * Y₂ N) := by ring
    filter_upwards [hX₂, hY₂, X₁.pos, X₂.pos, Y₁.pos, Y₂.pos] with N hX hY hX₁pos hX₂pos hY₁pos hY₂pos
    calc
      _ ≤ (CX * X₁ N) * (CY * Y₁ N) := by gcongr
      _ = (CX * CY) * (X₁ N * Y₁ N) := by ring
    )
}

def EventuallyPositive.order_mul {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : (X * Y).order = X.order * Y.order := by
  apply Quotient.sound
  simp [EventuallyPositive.asymp_iff]

instance OrderOfMagnitude.distrib {Ω:Type*} (f: Filter Ω) : Distrib (OrderOfMagnitude f) := {
  left_distrib := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    apply OrderOfMagnitude.ind; intro Z
    simp only [←EventuallyPositive.order_mul, ←EventuallyPositive.order_add, mul_add]
  right_distrib := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    apply OrderOfMagnitude.ind; intro Z
    simp only [←EventuallyPositive.order_mul, ←EventuallyPositive.order_add, add_mul]
}

instance OrderOfMagnitude.one {Ω:Type*} (f: Filter Ω) : One (OrderOfMagnitude f) :=
{
  one := EventuallyPositive.order (1 : EventuallyPositive f)
}

@[simp]
lemma EventuallyPositive.one_order {Ω:Type*} {f: Filter Ω} : (1 : EventuallyPositive f).order = 1 := rfl

noncomputable instance OrderOfMagnitude.inv {Ω:Type*} (f: Filter Ω) : Inv (OrderOfMagnitude f) :=
{
  inv := Quotient.lift (fun X ↦ (X⁻¹).order) (by
    intro X Y h
    simp
    rw [EventuallyPositive.order_eq_iff]
    simp [EventuallyPositive.asymp_iff] at h ⊢
    obtain ⟨ C, hC, h1, h2 ⟩ := h
    refine ⟨ C, hC, ?_, ?_ ⟩
    . filter_upwards [h2, X.pos, Y.pos] with N hX hXpos hYpos
      field_simp
      calc
        _ = C / (C * X N) := by field_simp
        _ ≤ C / Y N := by gcongr
    filter_upwards [h1, X.pos, Y.pos] with N hX hXpos hYpos
    field_simp
    calc
      _ = C / (C * Y N) := by field_simp
      _ ≤ C / X N := by gcongr
    )
}

def EventuallyPositive.order_inv {Ω:Type*} {f: Filter Ω} (X: EventuallyPositive f) : (X⁻¹).order = X.order⁻¹ := by
  apply Quotient.sound
  simp [EventuallyPositive.asymp_iff]

noncomputable instance OrderOfMagnitude.group {Ω:Type*} (f: Filter Ω) : Group (OrderOfMagnitude f) := Group.ofLeftAxioms
(by
  apply OrderOfMagnitude.ind; intro X
  apply OrderOfMagnitude.ind; intro Y
  apply OrderOfMagnitude.ind; intro Z
  simp only [←EventuallyPositive.order_mul, mul_assoc]
  )
(by
  apply OrderOfMagnitude.ind; intro X
  simp only [←EventuallyPositive.one_order, ←EventuallyPositive.order_mul, one_mul]
  )
(by
  apply OrderOfMagnitude.ind; intro X
  simp only [←EventuallyPositive.order_inv, ←EventuallyPositive.order_mul, ←EventuallyPositive.one_order, EventuallyPositive.order_eq_iff]
  apply EventuallyPositive.asymp_of_eventual_eq
  filter_upwards [X.pos] with N hN
  simp; field_simp
)

def EventuallyPositive.order_div {Ω:Type*} {f: Filter Ω} (X Y: EventuallyPositive f) : (X / Y).order = X.order / Y.order := by
  apply Quotient.sound
  apply EventuallyPositive.asymp_of_eventual_eq
  filter_upwards [Y.pos] with N hN
  simp; rfl

noncomputable instance OrderOfMagnitude.commGroup {Ω:Type*} (f: Filter Ω) : CommGroup (OrderOfMagnitude f) :=
{
  mul_comm := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    simp only [←EventuallyPositive.order_mul, mul_comm]
}

instance OrderOfMagnitude.orderedMonoid {Ω:Type*} (f: Filter Ω) : IsOrderedMonoid (OrderOfMagnitude f) :=
 {
  mul_le_mul_left := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    intro hXY
    apply OrderOfMagnitude.ind; intro Z
    simp [←EventuallyPositive.order_mul, EventuallyPositive.order_le, EventuallyPositive.le_iff] at hXY ⊢
    obtain ⟨ C, hC, hXY ⟩ := hXY
    refine ⟨ C, hC, ?_ ⟩
    filter_upwards [hXY, Z.pos] with N hXY hZpos
    calc
      _ ≤ Z N * (C * Y N) := by
        gcongr
      _ = C * (Z N * Y N) := by ring
  mul_le_mul_right := by
    apply OrderOfMagnitude.ind; intro X
    apply OrderOfMagnitude.ind; intro Y
    intro hXY
    apply OrderOfMagnitude.ind; intro Z
    simp [←EventuallyPositive.order_mul, EventuallyPositive.order_le, EventuallyPositive.le_iff] at hXY ⊢
    obtain ⟨ C, hC, hXY ⟩ := hXY
    refine ⟨ C, hC, ?_ ⟩
    filter_upwards [hXY, Z.pos] with N hXY hZpos
    calc
      _ ≤ (C * Y N) * Z N := by
        gcongr
      _ = C * (Y N * Z N) := by ring
 }

noncomputable instance OrderOfMagnitude.hasPow {Ω:Type*} (f: Filter Ω) : Pow (OrderOfMagnitude f) ℝ :=
{
  pow := fun X α => Quotient.lift (fun Y ↦ (Y ^ α).order) (by
    intro X Y h
    simp
    rw [EventuallyPositive.order_eq_iff]
    simp [EventuallyPositive.asymp_iff] at h ⊢
    obtain ⟨ C, hC, h1, h2 ⟩ := h
    rcases le_or_gt α 0 with h | h
    . refine ⟨ C ^ (-α), ?_, ?_, ?_ ⟩
      . positivity
      . filter_upwards [h2, X.pos, Y.pos] with N hX hXpos hYpos
        calc
          _ = C^(-α) * (C * (X N))^α := by
            rw [Real.mul_rpow (le_of_lt hC) (le_of_lt hXpos), ←mul_assoc, ←Real.rpow_add hC]
            simp
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.rpow_le_rpow_of_nonpos hYpos hX h
      filter_upwards [h1, X.pos, Y.pos] with N hY hXpos hYpos
      calc
        _ = C^(-α) * (C * (Y N))^α := by
          rw [Real.mul_rpow (le_of_lt hC) (le_of_lt hYpos), ←mul_assoc, ←Real.rpow_add hC]
          simp
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_nonpos hXpos hY h
    refine ⟨ C ^ α, Real.rpow_pos_of_pos hC α, ?_, ?_ ⟩
    . filter_upwards [h1, X.pos, Y.pos] with N hX hXpos hYpos
      calc
        _ ≤ (C * Y N) ^ α := by gcongr
        _ = C ^ α * (Y N ^ α) := by rw [Real.mul_rpow (le_of_lt hC) (le_of_lt hYpos)]
    filter_upwards [h2, X.pos, Y.pos] with N hY hXpos hYpos
    calc
      _ ≤ (C * X N) ^ α := by gcongr
      _ = C^α * (X N ^ α) := by rw [Real.mul_rpow (le_of_lt hC) (le_of_lt hXpos)]
  ) X
}
