import Mathlib.Data.Real.Hyperreal
import EstimateTools.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.MinimalAxioms


abbrev PositiveHyperreal := { x : Hyperreal // 0 < x }

noncomputable def Real.toPositiveHyperreal (x : ℝ) (hx : 0 < x) : PositiveHyperreal := ⟨ x, Hyperreal.coe_pos.mpr hx ⟩

@[simp]
lemma Real.toPositiveHyperreal_coe (x:ℝ) (hx:0<x) : (Real.toPositiveHyperreal x hx : Hyperreal) = x := by
  rfl

/-- The asymptotic preorder in the positive hyperreals. -/
def PositiveHyperreal.asym_preorder : Preorder PositiveHyperreal :=
{
  le := fun X Y => ∃ C:ℝ, C > 0 ∧ (X : Hyperreal) ≤ C * Y
  lt := fun X Y => ∀ ε:ℝ, ε>0 → (X : Hyperreal) ≤ ε * Y
  le_refl := fun X => ⟨1, by norm_num⟩
  le_trans := fun X Y Z => by
    rintro ⟨C1, hC1, hXY⟩ ⟨C2, hC2, hYZ⟩
    use C1 * C2
    refine ⟨ (by norm_num [hC1, hC2]), ?_ ⟩
    apply hXY.trans
    calc
      _ ≤ C1 * (C2 * (Z:Hyperreal)) := by
        apply (mul_le_mul_left _).mpr hYZ
        norm_num [hC1]
      _ = _ := by
        simp only [Hyperreal.coe_mul, mul_assoc]
  lt_iff_le_not_le := fun X Y => by
    constructor
    . intro h
      constructor
      . refine ⟨ 1, by norm_num, h 1 (by norm_num) ⟩
      by_contra! h2
      obtain ⟨ C, hC, h2 ⟩ := h2
      replace h := h (C⁻¹/2) (by positivity)
      have hXpos := X.property
      have hYpos := Y.property
      have hC' := Hyperreal.coe_pos.mpr hC
      have hC'' : ((C⁻¹:ℝ):Hyperreal) > 0 := Hyperreal.coe_pos.mpr (by positivity)
      have : (2:Hyperreal) ≤ 1 := calc
        _ = 2 * (X:Hyperreal)⁻¹ * X := by field_simp
        _ ≤ 2 * (X:Hyperreal)⁻¹ * ((C⁻¹/2:ℝ) * (Y:Hyperreal)) := by gcongr
        _ = (C⁻¹ * (X:Hyperreal)⁻¹) * Y := by field_simp; ring
        _ ≤ (C⁻¹ * (X:Hyperreal)⁻¹) * (C * X) := by gcongr
        _ = _ := by field_simp
      linarith
    intro ⟨ h1, h2 ⟩ ε hε
    contrapose! h2
    refine ⟨ ε⁻¹, by positivity, ?_ ⟩
    have hε' := Hyperreal.coe_pos.mpr hε
    have hε'' : ((ε⁻¹:ℝ):Hyperreal) > 0 := Hyperreal.coe_pos.mpr (by positivity)
    calc
      _ = (ε⁻¹:ℝ) * (ε * (Y:Hyperreal)) := by field_simp
      _ ≤ _ := by gcongr
}

abbrev PositiveHyperreal.lesssim (X Y : PositiveHyperreal) := PositiveHyperreal.asym_preorder.le X Y

abbrev PositiveHyperreal.ll (X Y : PositiveHyperreal) := PositiveHyperreal.asym_preorder.lt X Y

abbrev PositiveHyperreal.gtrsim (X Y : PositiveHyperreal) := PositiveHyperreal.asym_preorder.le Y X

abbrev PositiveHyperreal.gg (X Y : PositiveHyperreal) := PositiveHyperreal.asym_preorder.lt Y X

abbrev PositiveHyperreal.asymp (X Y : PositiveHyperreal) := X.lesssim Y ∧ Y.lesssim X

abbrev OrderOfMagnitude := OrderQuotient PositiveHyperreal.asym_preorder

abbrev PositiveHyperreal.order (X : PositiveHyperreal) : OrderOfMagnitude := PositiveHyperreal.asym_preorder.quotient X

lemma PositiveHyperreal.order_surjective : Function.Surjective PositiveHyperreal.order := Quot.mk_surjective

lemma PositiveHyperreal.order_eq_iff {X Y : PositiveHyperreal} :
  X.order = Y.order ↔ X.asymp Y := by
  convert PositiveHyperreal.asym_preorder.quot_eq_iff X Y

lemma PositiveHyperreal.order_le_iff {X Y : PositiveHyperreal} : X.order ≤ Y.order ↔ X.lesssim Y := by
  convert PositiveHyperreal.asym_preorder.quot_le_iff _ _

lemma PositiveHyperreal.order_lt_iff {X Y : PositiveHyperreal} : X.order < Y.order ↔ X.ll Y := by
  convert PositiveHyperreal.asym_preorder.quot_lt_iff _ _

noncomputable instance OrderOfMagnitude.linearOrder : LinearOrder OrderOfMagnitude := PositiveHyperreal.asym_preorder.quot_linear (by
   intro X Y
   rcases lt_or_ge (X:Hyperreal) Y with h | h
   . left
     refine ⟨ 1, by norm_num, ?_ ⟩
     simp only [Hyperreal.coe_one, one_mul]
     exact le_of_lt h
   right
   refine ⟨ 1, by norm_num, ?_ ⟩
   simp only [Hyperreal.coe_one, one_mul]
   exact h
  )

noncomputable instance OrderOfMagnitude.one : One OrderOfMagnitude := ⟨ PositiveHyperreal.order 1 ⟩

@[simp]
lemma PositiveHyperreal.order_one : (1:PositiveHyperreal).order = 1 := by
  rfl

@[simp]
lemma Real.order_of_pos (x : ℝ) (hx : 0 < x) : (x.toPositiveHyperreal hx).order = 1 := by
  rw [←PositiveHyperreal.order_one, PositiveHyperreal.order_eq_iff]
  constructor
  . refine ⟨ x, hx, ?_ ⟩
    simp
  refine ⟨ x⁻¹, by positivity, ?_ ⟩
  have := Hyperreal.coe_pos.mpr hx
  field_simp

noncomputable instance OrderOfMagnitude.add : Add OrderOfMagnitude := {
  add := Quotient.lift₂ (fun x y => (x + y).order)
    (by
     intro X Y Z W hXZ hYW
     simp [PositiveHyperreal.order_eq_iff]
     replace hXZ := (PositiveHyperreal.asym_preorder.equiv_iff X Z).mp hXZ
     replace hYW := (PositiveHyperreal.asym_preorder.equiv_iff Y W).mp hYW
     have hX := X.property
     have hY := Y.property
     have hZ := Z.property
     have hW := W.property
     constructor
     . obtain ⟨ C1, hC1, h1 ⟩ := hXZ.1
       obtain ⟨ C2, hC2, h2 ⟩ := hYW.1
       refine ⟨ max C1 C2, by positivity, ?_ ⟩
       simp only [Positive.coe_add, Hyperreal.coe_max]
       calc
         _ ≤ C1 * (Z:Hyperreal) + C2 * (W:Hyperreal) := by
           gcongr
         _ ≤ (max C1 C2) * (Z:Hyperreal) + (max C1 C2) * (W:Hyperreal) := by
           gcongr
           . simp only [Hyperreal.coe_max, le_sup_left]
           simp only [Hyperreal.coe_max, le_sup_right]
         _ = _ := by simp [Hyperreal.coe_max, mul_add]
     obtain ⟨ C1, hC1, h1 ⟩ := hXZ.2
     obtain ⟨ C2, hC2, h2 ⟩ := hYW.2
     refine ⟨ max C1 C2, by positivity, ?_ ⟩
     simp only [Positive.coe_add, Hyperreal.coe_max]
     calc
       _ ≤ C1 * (X:Hyperreal) + C2 * (Y:Hyperreal) := by
         gcongr
       _ ≤ (max C1 C2) * (X:Hyperreal) + (max C1 C2) * (Y:Hyperreal) := by
         gcongr
         . simp only [Hyperreal.coe_max, le_sup_left]
         simp only [Hyperreal.coe_max, le_sup_right]
       _ = _ := by simp [Hyperreal.coe_max, mul_add]
     )
}

@[simp]
lemma OrderOfMagnitude.add_eq_max (X Y: OrderOfMagnitude) : X + Y = max X Y := by
  sorry

noncomputable instance OrderOfMagnitude.addCommSemigroup  : AddCommSemigroup (OrderOfMagnitude) :=
{
  add_assoc := by
    sorry
  add_comm := by
    sorry
}

lemma OrderOfMagnitude.add_self (X: OrderOfMagnitude) : X + X = X := by
  simp only [add_eq_max, max_self]

@[simp]
lemma PositiveHyperreal.order_add (X Y: PositiveHyperreal) : (X+Y).order = X.order + Y.order := by
  apply Quotient.sound
  convert Setoid.refl (X + Y)

noncomputable instance OrderOfMagnitude.mul : Mul OrderOfMagnitude := {
  mul  := Quotient.lift₂ (fun x y => (x * y).order)
    (by
    intro X Y Z W hXZ hYW
    simp [PositiveHyperreal.order_eq_iff]
    replace hXZ := (PositiveHyperreal.asym_preorder.equiv_iff X Z).mp hXZ
    replace hYW := (PositiveHyperreal.asym_preorder.equiv_iff Y W).mp hYW
    have hX := X.property
    have hY := Y.property
    have hZ := Z.property
    have hW := W.property
    constructor
    . obtain ⟨ C1, hC1, h1 ⟩ := hXZ.1
      obtain ⟨ C2, hC2, h2 ⟩ := hYW.1
      have hC1' := Hyperreal.coe_pos.mpr hC1
      have hC2' := Hyperreal.coe_pos.mpr hC2
      refine ⟨ C1 * C2, by positivity, ?_ ⟩
      simp only [Positive.val_mul, Hyperreal.coe_mul]
      calc
        _ ≤ (C1 * (Z:Hyperreal)) * (C2 * (W:Hyperreal)) := by
          gcongr
        _ = _ := by ring
    obtain ⟨ C1, hC1, h1 ⟩ := hXZ.2
    obtain ⟨ C2, hC2, h2 ⟩ := hYW.2
    have hC1' := Hyperreal.coe_pos.mpr hC1
    have hC2' := Hyperreal.coe_pos.mpr hC2
    refine ⟨ C1 * C2, by positivity, ?_ ⟩
    simp only [Positive.val_mul, Hyperreal.coe_mul]
    calc
      _ ≤ (C1 * (X:Hyperreal)) * (C2 * (Y:Hyperreal)) := by
        gcongr
      _ = _ := by ring
    )
}

@[simp]
lemma PositiveHyperreal.order_mul (X Y: PositiveHyperreal) : (X*Y).order = X.order * Y.order := by
  apply Quotient.sound
  convert Setoid.refl (X * Y)

noncomputable instance Hyperreal.pow : Pow Hyperreal Hyperreal := ⟨ Filter.Germ.map₂ Real.rpow ⟩

noncomputable abbrev to_hyperreal (x: ℕ → ℝ) : Hyperreal := Filter.Germ.ofFun x

noncomputable instance pow_fn : Pow (ℕ → ℝ) (ℕ → ℝ) := {
  pow := fun x y ↦ fun n ↦ x n ^ y n
}

@[simp]
lemma pow_fn_eq (x y : ℕ → ℝ) (n:ℕ): (x ^ y) n = x n ^ y n := rfl

@[simp]
lemma pow_fn_zero (x : ℕ → ℝ) : (x ^ (0 : ℕ → ℝ)) = 1 := by
  funext n
  simp [pow_fn_eq, zero_pow]

@[simp]
lemma Hyperreal.coe_pow (x y : ℕ → ℝ) : (to_hyperreal x) ^ (to_hyperreal y) = to_hyperreal (x ^ y) := rfl

@[simp]
lemma Hyperreal.coe_mul_fn (x y : ℕ → ℝ) : (to_hyperreal x) * (to_hyperreal y) = to_hyperreal (x * y) := rfl

@[simp]
lemma Hyperreal.coe_add_fn (x y : ℕ → ℝ) : (to_hyperreal x) + (to_hyperreal y) = to_hyperreal (x + y) := rfl

lemma Hyperreal.coe_zero_fn : (to_hyperreal 0) = 0 := rfl

lemma Hyperreal.lt_def : ((· < ·): Hyperreal → Hyperreal → Prop) = Filter.Germ.LiftRel (· < ·) := Filter.Germ.lt_def

lemma Hyperreal.le_def : ((· ≤ ·): Hyperreal → Hyperreal → Prop) = Filter.Germ.LiftRel (· ≤ ·) := by
  ext ⟨x⟩ ⟨y⟩
  exact Filter.Germ.coe_le

lemma Hyperreal.gt_def : ((· > ·): Hyperreal → Hyperreal → Prop) = Filter.Germ.LiftRel (· > ·) := by
  ext ⟨x⟩ ⟨y⟩
  simp [Hyperreal.lt_def]

lemma Hyperreal.ge_def : ((· ≥ ·): Hyperreal → Hyperreal → Prop) = Filter.Germ.LiftRel (· ≥ ·) := by
  ext ⟨x⟩ ⟨y⟩
  simp [Hyperreal.le_def]

lemma Hyperreal.pow_of_pos {x : Hyperreal} (y:Hyperreal) : x > 0 → x^y > 0 := by
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  simp only [Filter.Germ.quot_mk_eq_coe, gt_iff_lt, congrFun₂ Hyperreal.gt_def, Hyperreal.coe_pow, ←Hyperreal.coe_zero_fn, Filter.Germ.liftRel_coe]
  intro h
  apply Filter.Eventually.mp h (Filter.Eventually.of_forall _)
  intro n
  simp only [pow_fn_eq]
  exact fun a ↦ Real.rpow_pos_of_pos a (Y n)

noncomputable instance PositiveHyperreal.pow : Pow PositiveHyperreal Hyperreal := {
  pow := fun X y ↦ ⟨ X.val ^ y, Hyperreal.pow_of_pos y X.property ⟩
}

@[simp]
lemma PositiveHyperreal.pow_coe (X:PositiveHyperreal) (y:Hyperreal) : (X^y : PositiveHyperreal) = (X:Hyperreal)^y := rfl

lemma Hyperreal.pow_le_pow {x y:Hyperreal} {z:Hyperreal} (hx: x ≥ 0) (hz: z ≥ 0) (hxy: x ≤ y) : x^z ≤ y^z := by
  revert hxy hz hx
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx hz hxy
  simp only [congrFun₂ Hyperreal.le_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn] at hx hz hxy ⊢
  filter_upwards [hz, hx, hxy] with n hzn hxn hxyn
  simp only [Pi.zero_apply] at hzn hxn
  exact Real.rpow_le_rpow hxn hxyn hzn

lemma Hyperreal.pow_le_pow' {x y:Hyperreal} {z:Hyperreal} (hx: x > 0) (hz: z < 0) (hxy: x ≤ y) : x^z ≥ y^z := by
  revert hx hz hxy
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx hz hxy
  simp only [congrFun₂ Hyperreal.ge_def _ _, congrFun₂ Hyperreal.lt_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn] at hx hz hxy ⊢
  filter_upwards [hz, hx, hxy] with n hzn hxn hxyn
  simp only [Pi.zero_apply] at hzn hxn
  apply Real.rpow_le_rpow_of_nonpos hxn hxyn (le_of_lt hzn)

lemma Hyperreal.mul_pow {x y:Hyperreal} (hx: x ≥ 0) (hy: y ≥ 0) (z:Hyperreal) : (x*y)^z = x^z * y^z := by
  revert hx hy
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx hy
  simp only [congrFun₂ Hyperreal.le_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn, Hyperreal.coe_pow, Hyperreal.coe_mul_fn _ _] at hx hy ⊢
  rw [Filter.Germ.coe_eq]
  filter_upwards [hx, hy] with n hxn hyn
  simp only [pow_fn_eq, Pi.mul_apply, Pi.zero_apply] at hxn hyn ⊢
  exact Real.mul_rpow hxn hyn

lemma Hyperreal.pow_add {x:Hyperreal} (hx: x > 0) (y z:Hyperreal) : x^(y+z) = x^y * x^z := by
  revert hx
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx
  simp only [congrFun₂ Hyperreal.lt_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn, Hyperreal.coe_pow, Hyperreal.coe_add_fn _ _, Hyperreal.coe_mul_fn _ _] at hx ⊢
  rw [Filter.Germ.coe_eq]
  filter_upwards [hx] with n hxn
  simp only [pow_fn_eq, Pi.add_apply, Pi.zero_apply] at hxn ⊢
  exact Real.rpow_add hxn _ _

@[simp]
lemma Hyperreal.pow_zero (x:Hyperreal) : x^(0:Hyperreal) = 1 := by
  apply Quot.ind _ x; intro X
  simp only [Filter.Germ.quot_mk_eq_coe, ←Hyperreal.coe_zero_fn, Hyperreal.coe_pow, pow_fn_zero, Filter.Germ.coe_one]

noncomputable instance OrderOfMagnitude.pow : Pow OrderOfMagnitude Real := {
  pow  := fun X y ↦ (Quotient.lift (fun x => (x ^ (y:Hyperreal)).order)
    (by
      intro X Y hXY
      obtain ⟨ ⟨ C₁, hC₁, h1 ⟩, ⟨ C₂, hC₂, h2 ⟩ ⟩ := (PositiveHyperreal.asym_preorder.equiv_iff X Y).mp hXY
      have hC₁' := Hyperreal.coe_pos.mpr hC₁
      have hC₂' := Hyperreal.coe_pos.mpr hC₂
      have hX := X.property
      have hY := Y.property
      simp [PositiveHyperreal.order_eq_iff]
      constructor
      . rcases lt_or_ge y 0 with hy | hy
        . refine ⟨ C₂ ^ (-y), by positivity, ?_ ⟩
          simp only [PositiveHyperreal.pow_coe]
          calc
            _ = (C₂:Hyperreal) ^ (-y:Hyperreal) * (C₂:Hyperreal) ^ (y:Hyperreal) * (X:Hyperreal)^(y:Hyperreal) := by
              convert (one_mul _).symm
              simp [←Hyperreal.pow_add hC₂']
            _ = (C₂:Hyperreal) ^ (-y:Hyperreal) * ((C₂:Hyperreal) * X)^(y:Hyperreal) := by
              rw [mul_assoc]
              congr; symm
              apply Hyperreal.mul_pow (le_of_lt hC₂') (le_of_lt hX) _
            _ ≤ _ := by
              gcongr
              . apply le_of_lt (Hyperreal.pow_of_pos _ _)
                positivity
              . simp; positivity
              . apply le_refl
              apply Hyperreal.pow_le_pow' hY _ h2
              convert Hyperreal.coe_lt_coe.mpr hy
        refine ⟨ C₁ ^ y, by positivity, ?_ ⟩
        simp only [PositiveHyperreal.pow_coe]
        calc
          _ ≤ ((C₁:Hyperreal) * Y) ^ (y:Hyperreal) := Hyperreal.pow_le_pow (le_of_lt X.property) (Hyperreal.coe_nonneg.mpr hy) h1
          _ = _ := Hyperreal.mul_pow (le_of_lt hC₁') (le_of_lt Y.property) _
      rcases lt_or_ge y 0 with hy | hy
      . refine ⟨ C₁ ^ (-y), by positivity, ?_ ⟩
        simp only [PositiveHyperreal.pow_coe]
        calc
          _ = (C₁:Hyperreal) ^ (-y:Hyperreal) * (C₁:Hyperreal) ^ (y:Hyperreal) * (Y:Hyperreal)^(y:Hyperreal) := by
            convert (one_mul _).symm
            simp [←Hyperreal.pow_add hC₁']
          _ = (C₁:Hyperreal) ^ (-y:Hyperreal) * ((C₁:Hyperreal) * Y)^(y:Hyperreal) := by
            rw [mul_assoc]
            congr; symm
            apply Hyperreal.mul_pow (le_of_lt hC₁') (le_of_lt hY) _
          _ ≤ _ := by
            gcongr
            . apply le_of_lt (Hyperreal.pow_of_pos _ _)
              positivity
            . simp; positivity
            . apply le_refl
            apply Hyperreal.pow_le_pow' hX _ h1
            convert Hyperreal.coe_lt_coe.mpr hy
      refine ⟨ C₂ ^ y, by positivity, ?_ ⟩
      simp only [PositiveHyperreal.pow_coe]
      calc
        _ ≤ ((C₂:Hyperreal) * X) ^ (y:Hyperreal) := Hyperreal.pow_le_pow (le_of_lt Y.property) (Hyperreal.coe_nonneg.mpr hy) h2
        _ = _ := Hyperreal.mul_pow (le_of_lt hC₂') (le_of_lt X.property) _
    ) X)
}

@[simp]
lemma PositiveHyperreal.order_pow (X: PositiveHyperreal) (y: ℝ) : (X^(y:Hyperreal)).order = X.order ^ y := by
  apply Quotient.sound
  simp only [Setoid.refl]


noncomputable instance OrderOfMagnitude.inv : Inv OrderOfMagnitude := ⟨ fun X ↦ X ^ (-1:ℝ) ⟩

noncomputable instance OrderOfMagnitude.group  : Group (OrderOfMagnitude) := Group.ofLeftAxioms
(by
  sorry
  )
(by
  sorry
  )
(by
  sorry
)

noncomputable instance OrderOfMagnitude.comm_group  : CommGroup (OrderOfMagnitude) := {
  mul_comm := by
    sorry
}


instance OrderOfMagnitude.orderedMonoid  : IsOrderedMonoid OrderOfMagnitude := {
  mul_le_mul_left := by sorry
  mul_le_mul_right := by sorry
}

noncomputable instance OrderOfMagnitude.distrib : Distrib OrderOfMagnitude := {
  left_distrib := by
    sorry
  right_distrib := by
    sorry
}
