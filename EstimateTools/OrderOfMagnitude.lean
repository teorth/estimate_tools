import Mathlib.Data.Real.Hyperreal
import EstimateTools.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.TypeTags.Basic
import Canonical


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
lemma PositiveHyperreal.order_add (X Y: PositiveHyperreal) : (X+Y).order = X.order + Y.order := by
  apply Quotient.sound
  convert Setoid.refl (X + Y)

@[simp]
lemma OrderOfMagnitude.add_eq_max (X Y: OrderOfMagnitude) : X + Y = max X Y := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  rcases le_or_gt x y with h | h
  . have : x.order ≤ y.order := by
      rw [PositiveHyperreal.order_le_iff]
      refine ⟨1, by norm_num, ?_ ⟩
      simp [h]
    simp only [sup_of_le_right this, <-PositiveHyperreal.order_add, PositiveHyperreal.order_eq_iff]
    constructor
    . refine ⟨ (2:ℝ), by norm_num, ?_ ⟩
      simp
      have : (x:Hyperreal) ≤ y := h
      linarith
    refine ⟨ 1, by norm_num, ?_ ⟩
    simp [le_of_lt x.property]
  have : y.order ≤ x.order := by
    rw [PositiveHyperreal.order_le_iff]
    refine ⟨1, by norm_num, ?_ ⟩
    simp [le_of_lt h]
  simp only [sup_of_le_left this, <-PositiveHyperreal.order_add, PositiveHyperreal.order_eq_iff]
  constructor
  . refine ⟨ (2:ℝ), by norm_num, ?_ ⟩
    simp
    have : (y:Hyperreal) ≤ x := le_of_lt h
    linarith
  refine ⟨ 1, by norm_num, ?_ ⟩
  simp [le_of_lt y.property]

noncomputable instance OrderOfMagnitude.addCommSemigroup  : AddCommSemigroup (OrderOfMagnitude) :=
{
  add_assoc := by
    simp [max_assoc]
  add_comm := by
    simp [max_comm]
}

lemma OrderOfMagnitude.add_self (X: OrderOfMagnitude) : X + X = X := by
  simp only [add_eq_max, max_self]

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

lemma to_hyperreal_surjective : Function.Surjective to_hyperreal := by
  convert Quotient.mk'_surjective

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

lemma Hyperreal.coe_pow' (x y: ℝ) : (x:Hyperreal) ^ (y:Hyperreal) = (x^y:ℝ) := rfl

@[simp]
lemma Hyperreal.coe_mul_fn (x y : ℕ → ℝ) : (to_hyperreal x) * (to_hyperreal y) = to_hyperreal (x * y) := rfl

@[simp]
lemma Hyperreal.coe_add_fn (x y : ℕ → ℝ) : (to_hyperreal x) + (to_hyperreal y) = to_hyperreal (x + y) := rfl

@[simp]
lemma Hyperreal.coe_zero_fn : (to_hyperreal 0) = 0 := rfl

@[simp]
lemma Hyperreal.coe_one_fn : (to_hyperreal 1) = 1 := rfl

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

@[simp]
lemma Hyperreal.pow_of_one (y: Hyperreal) : (1:Hyperreal)^y = 1 := by
  apply Quot.ind _ y; intro Y
  simp only [←Hyperreal.coe_one_fn]
  convert Hyperreal.coe_pow _ _
  ext N
  simp only [Pi.one_apply, pow_fn_eq, Real.one_rpow]

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

lemma Hyperreal.pow_le_pow' {x y:Hyperreal} {z:Hyperreal} (hx: x > 0) (hz: z ≤ 0) (hxy: x ≤ y) : x^z ≥ y^z := by
  revert hx hz hxy
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx hz hxy
  simp only [congrFun₂ Hyperreal.ge_def _ _, congrFun₂ Hyperreal.lt_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn] at hx hz hxy ⊢
  filter_upwards [hz, hx, hxy] with n hzn hxn hxyn
  simp only [Pi.zero_apply] at hzn hxn
  apply Real.rpow_le_rpow_of_nonpos hxn hxyn hzn

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

lemma Hyperreal.pow_mul {x:Hyperreal} (hx: x > 0) (y z:Hyperreal) : x^(y*z) = (x^y)^z := by
  revert hx
  apply Quot.ind _ x; intro X
  apply Quot.ind _ y; intro Y
  apply Quot.ind _ z; intro Z
  simp
  intro hx
  simp only [congrFun₂ Hyperreal.lt_def _ _, Filter.Germ.liftRel_coe, pow_fn_eq, ←Hyperreal.coe_zero_fn, Hyperreal.coe_pow, Hyperreal.coe_mul_fn _ _] at hx ⊢
  rw [Filter.Germ.coe_eq]
  filter_upwards [hx] with n hxn
  simp only [pow_fn_eq, Pi.mul_apply, Pi.zero_apply] at hxn ⊢
  apply Real.rpow_mul (le_of_lt hxn) _ _

@[simp]
lemma Hyperreal.pow_zero (x:Hyperreal) : x^(0:Hyperreal) = 1 := by
  apply Quot.ind _ x; intro X
  simp only [Filter.Germ.quot_mk_eq_coe, ←Hyperreal.coe_zero_fn, Hyperreal.coe_pow, pow_fn_zero, Filter.Germ.coe_one]

@[simp]
lemma Hyperreal.pow_one (x:Hyperreal) : x^(1:Hyperreal) = x := by
  apply Quot.ind _ x; intro X
  simp only [Filter.Germ.quot_mk_eq_coe, ←Hyperreal.coe_one_fn, Hyperreal.coe_pow]
  congr
  ext n
  simp only [pow_fn_eq, Pi.one_apply, Real.rpow_one]


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
              apply Hyperreal.pow_le_pow' hY (le_of_lt _) h2
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
            apply Hyperreal.pow_le_pow' hX (le_of_lt _) h1
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

@[simp]
lemma OrderOfMagnitude.pow_one (X: OrderOfMagnitude) : (X^(1:ℝ)) = X := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp [←PositiveHyperreal.order_pow]
  congr
  simp [Subtype.eq_iff, PositiveHyperreal.pow_coe]

@[simp]
lemma OrderOfMagnitude.pow_zero (X: OrderOfMagnitude) : (X^(0:ℝ)) = 1 := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp [←PositiveHyperreal.order_pow]
  congr
  simp [Subtype.eq_iff, PositiveHyperreal.pow_coe]



noncomputable instance OrderOfMagnitude.inv : Inv OrderOfMagnitude := ⟨ fun X ↦ X ^ (-1:ℝ) ⟩


noncomputable instance OrderOfMagnitude.group  : Group (OrderOfMagnitude) := Group.ofLeftAxioms
(by
  intro X Y Z
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  obtain ⟨ z, rfl ⟩ := PositiveHyperreal.order_surjective Z
  simp only [←PositiveHyperreal.order_mul, PositiveHyperreal.order_eq_iff, mul_assoc]
  )
(by
  intro X
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp only [←PositiveHyperreal.order_one, ←PositiveHyperreal.order_mul, one_mul]
  )
(by
  intro X
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp only [OrderOfMagnitude.inv, ←PositiveHyperreal.order_pow, ←PositiveHyperreal.order_mul,  ←PositiveHyperreal.order_one]
  congr
  simp only [Hyperreal.coe_neg, Hyperreal.coe_one, Subtype.eq_iff, Positive.val_mul, PositiveHyperreal.pow_coe, Positive.val_one]
  nth_rewrite 2 [←Hyperreal.pow_one (x : Hyperreal)]
  rw [←Hyperreal.pow_add]
  simp
  exact x.property
)

@[simp]
lemma OrderOfMagnitude.div_eq (X Y:OrderOfMagnitude) : X / Y = X * Y^(-1:ℝ) := rfl

noncomputable instance OrderOfMagnitude.comm_group  : CommGroup (OrderOfMagnitude) := {
  mul_comm := by
    intro X Y
    obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
    obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
    simp only [←PositiveHyperreal.order_mul, mul_comm]
}


instance OrderOfMagnitude.orderedMonoid  : IsOrderedMonoid OrderOfMagnitude := {
  mul_le_mul_left := by
    intro X Y hXY Z
    obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
    obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
    obtain ⟨ z, rfl ⟩ := PositiveHyperreal.order_surjective Z
    simp only [←PositiveHyperreal.order_mul, PositiveHyperreal.order_le_iff] at hXY ⊢
    obtain ⟨ C, hC, h1 ⟩ := hXY
    refine ⟨ C, hC, ?_ ⟩
    simp only [Positive.val_mul]
    calc
      _ ≤ (z:Hyperreal) * (C * (y:Hyperreal)) := by
        gcongr
        exact le_of_lt z.property
      _ = _ := by ring
  mul_le_mul_right := by
    intro X Y hXY Z
    obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
    obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
    obtain ⟨ z, rfl ⟩ := PositiveHyperreal.order_surjective Z
    simp only [←PositiveHyperreal.order_mul, PositiveHyperreal.order_le_iff] at hXY ⊢
    obtain ⟨ C, hC, h1 ⟩ := hXY
    refine ⟨ C, hC, ?_ ⟩
    simp only [Positive.val_mul]
    calc
      _ ≤ (z:Hyperreal) * (C * (y:Hyperreal)) := by
        rw [mul_comm]
        have := le_of_lt z.property
        gcongr
      _ = _ := by ring
}

noncomputable instance OrderOfMagnitude.distrib : Distrib OrderOfMagnitude := {
  left_distrib := by
    intro X Y Z
    obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
    obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
    obtain ⟨ z, rfl ⟩ := PositiveHyperreal.order_surjective Z
    simp only [←PositiveHyperreal.order_mul, ←PositiveHyperreal.order_add, left_distrib]
  right_distrib := by
    intro X Y Z
    obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
    obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
    obtain ⟨ z, rfl ⟩ := PositiveHyperreal.order_surjective Z
    simp only [←PositiveHyperreal.order_mul, ←PositiveHyperreal.order_add, right_distrib]
}



lemma power_i (X Y: OrderOfMagnitude) (α: ℝ) : (X * Y)^α = X^α * Y^α := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  simp only [←PositiveHyperreal.order_mul, ←PositiveHyperreal.order_pow]
  congr
  simp [Subtype.eq_iff, PositiveHyperreal.pow_coe]
  exact Hyperreal.mul_pow (le_of_lt x.property) (le_of_lt y.property) _

lemma power_i' (X Y: OrderOfMagnitude) (α: ℝ) : (X / Y)^α = X^α / Y^α := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  simp only [OrderOfMagnitude.div_eq, ← PositiveHyperreal.order_pow, ←PositiveHyperreal.order_mul]
  congr
  simp [Subtype.eq_iff, PositiveHyperreal.pow_coe]
  rw [Hyperreal.mul_pow (le_of_lt x.property), ←Hyperreal.pow_mul y.property, ←Hyperreal.pow_mul y.property]
  . congr 2
    exact mul_comm _ _
  apply le_of_lt (Hyperreal.pow_of_pos _ y.property)

lemma power_ii (X: OrderOfMagnitude) (α: ℝ) : X^(α * β) = (X^α)^β := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp only [←PositiveHyperreal.order_pow]
  congr 1
  simp only [Hyperreal.coe_mul, Subtype.eq_iff, PositiveHyperreal.pow_coe, Hyperreal.pow_mul x.property _ _]

@[simp]
lemma power_iv (α: ℝ) : (1:OrderOfMagnitude)^α = 1 := by
  simp [←PositiveHyperreal.order_one, ←PositiveHyperreal.order_pow]
  congr
  simp only [Subtype.eq_iff, PositiveHyperreal.pow_coe]
  convert Hyperreal.pow_of_one _


lemma power_vi {X Y: OrderOfMagnitude} {α: ℝ} (hα: α ≥ 0) (hXY: X ≤ Y) : X^α ≤ Y^α := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  simp only [←PositiveHyperreal.order_pow] at ⊢
  rw [PositiveHyperreal.order_le_iff] at hXY ⊢
  obtain ⟨ C, hC, h1 ⟩ := hXY
  refine ⟨ C^α, by positivity, ?_ ⟩
  simp only [PositiveHyperreal.pow_coe]
  convert Hyperreal.pow_le_pow (le_of_lt x.property) (Hyperreal.coe_nonneg.mpr hα) h1 using 1
  rw [Hyperreal.mul_pow (Hyperreal.coe_nonneg.mpr (le_of_lt hC)) (le_of_lt y.property)]
  rfl

lemma power_v (X Y: OrderOfMagnitude) {α: ℝ} (hα: α ≥ 0): (X + Y)^α = X^α + Y^α := by
  simp only [OrderOfMagnitude.add_eq_max]
  rcases le_or_gt X Y with h | h
  . have h' := power_vi hα h
    rw [max_eq_right_iff.mpr h, max_eq_right_iff.mpr h']
  replace h := le_of_lt h
  have h' := power_vi hα h
  rw [max_eq_left_iff.mpr h, max_eq_left_iff.mpr h']

lemma power_vii (X Y: OrderOfMagnitude) {α: ℝ} (hα: α > 0) : X ≤ Y ↔ X^α ≤ Y^α := by
constructor
. intro h
  exact power_vi (le_of_lt hα) h
intro h
have : α * α⁻¹ = 1 := by field_simp
convert power_vi (le_of_lt (Right.inv_pos.mpr hα)) h
. rw [←power_ii, this, OrderOfMagnitude.pow_one]
rw [←power_ii, this, OrderOfMagnitude.pow_one]

lemma power_vii' (X Y: OrderOfMagnitude) {α: ℝ} (hα: α > 0) : X < Y ↔ X^α < Y^α := by
  rw [←not_iff_not]
  simp only [not_lt]
  exact power_vii Y X hα

lemma power_viii {X Y: OrderOfMagnitude} {α: ℝ} (hα: α ≤ 0) (hXY: X ≤ Y) : X^α ≥ Y^α := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  obtain ⟨ y, rfl ⟩ := PositiveHyperreal.order_surjective Y
  simp only [←PositiveHyperreal.order_pow] at ⊢
  rw [ge_iff_le]
  rw [PositiveHyperreal.order_le_iff] at hXY ⊢
  obtain ⟨ C, hC, h1 ⟩ := hXY
  refine ⟨ C^(-α), by positivity, ?_ ⟩
  simp only [PositiveHyperreal.pow_coe]
  replace h1 := Hyperreal.pow_le_pow' x.property (Hyperreal.coe_le_coe.mpr hα) h1
  have : y.val ^ (α:Hyperreal) = (C^(-α):ℝ) * (C*y.val)^(α:Hyperreal) := by
    rw [Hyperreal.mul_pow (Hyperreal.coe_nonneg.mpr (le_of_lt hC)) (le_of_lt y.property),← mul_assoc]
    convert (one_mul _).symm
    simp only [Hyperreal.coe_pow', ←Hyperreal.coe_mul, ←Real.rpow_add hC, neg_add_cancel, Real.rpow_zero, Hyperreal.coe_one]
  rw [this]
  gcongr
  simp only [Hyperreal.coe_nonneg]
  positivity


lemma power_ix (X Y: OrderOfMagnitude) {α: ℝ} (hα: α < 0): X ≤ Y ↔ X^α ≥ Y^α := by
  constructor
  . intro h
    exact power_viii (le_of_lt hα) h
  intro h
  have : α * α⁻¹ = 1 := mul_inv_cancel₀ $ Ne.symm $ ne_of_gt hα
  rw [ge_iff_le] at h
  rw [←ge_iff_le]
  convert power_viii (le_of_lt (inv_lt_zero.mpr hα)) h using 1
  . rw [←power_ii, this, OrderOfMagnitude.pow_one]
  rw [←power_ii, this, OrderOfMagnitude.pow_one]

lemma power_ix' (X Y: OrderOfMagnitude) {α: ℝ} (hα: α < 0): X < Y ↔ X^α > Y^α := by
  rw [←not_iff_not]
  simp only [not_lt]
  exact power_ix Y X hα

lemma power_x (X: OrderOfMagnitude) (α β: ℝ) : X^(α+β) = X^α * X^β := by
  obtain ⟨ x, rfl ⟩ := PositiveHyperreal.order_surjective X
  simp only [←PositiveHyperreal.order_pow]
  congr
  simp only [Hyperreal.coe_add, Subtype.eq_iff, PositiveHyperreal.pow_coe]
  exact Hyperreal.pow_add x.property _ _

abbrev LogOrderOfMagnitude := Additive OrderOfMagnitude

abbrev OrderOfMagnitude.log : OrderOfMagnitude ≃ LogOrderOfMagnitude := Additive.ofMul

abbrev LogOrderOfMagnitude.exp : LogOrderOfMagnitude ≃ OrderOfMagnitude := OrderOfMagnitude.log.symm

def OrderOfMagnitude.log_ordered : OrderOfMagnitude ≃o LogOrderOfMagnitude := {
  toFun := OrderOfMagnitude.log
  invFun := LogOrderOfMagnitude.exp
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intros
    simp only [Additive.ofMul_symm_eq, Equiv.coe_fn_mk, Additive.ofMul_le]
}

def LogOrderOfMagnitude.exp_ordered : LogOrderOfMagnitude ≃o  OrderOfMagnitude := OrderOfMagnitude.log_ordered.symm

noncomputable instance LogOrderOfMagnitude.linear_order : LinearOrder LogOrderOfMagnitude := @Additive.linearOrder OrderOfMagnitude OrderOfMagnitude.linearOrder

@[simp]
lemma OrderOfMagnitude.log_mul (X Y: OrderOfMagnitude) : (X * Y).log = X.log + Y.log := rfl

@[simp]
lemma OrderOfMagnitude.log_add (X Y: OrderOfMagnitude) : (X + Y).log = max X.log Y.log := by
  rw [OrderOfMagnitude.add_eq_max]
  rfl

@[simp]
lemma OrderOfMagnitude.log_div (X Y: OrderOfMagnitude) : (X / Y).log = X.log - Y.log := rfl

@[simp]
lemma OrderOfMagnitude.log_one : (1:OrderOfMagnitude).log = 0 := rfl

lemma OrderOfMagnitude.log_const (C: ℝ) (hC: C > 0) : (C.toPositiveHyperreal hC).order.log = 0 := by
  rw [Real.order_of_pos C hC]
  exact OrderOfMagnitude.log_one -- which is rfl


noncomputable instance LogOrderOfMagnitude.vec : Module ℝ LogOrderOfMagnitude := {
  smul := fun α x ↦ (x.exp ^ α).log
  one_smul := by
    intro x
    change (x.exp ^ (1:ℝ)).log = x.log
    simp
    rfl
  mul_smul := by
    intro α β x
    change (x.exp ^ (α * β)).log = (((x.exp ^ β).log).exp ^ α).log
    simp [mul_comm α β]
    exact power_ii (Additive.toMul x) β
  smul_zero := by
    intro α
    change ((0:LogOrderOfMagnitude).exp^α).log = 0
    simp
  smul_add := by
    intro α x y
    change ((x + y).exp ^ α).log = (x.exp ^ α).log + (y.exp ^ α).log
    simp only [Additive.ofMul_symm_eq, toMul_add, power_i, ofMul_mul]
  add_smul := by
    intro α β x
    change (x.exp ^ (α+β)).log = (x.exp ^ α).log + (x.exp ^ β).log
    simp only [Additive.ofMul_symm_eq, power_x, ofMul_mul]
  zero_smul := by
    intro x
    change (x.exp^(0:ℝ)).log = 0
    simp
}

lemma LogOrderOfMagnitude.smul_def (α: ℝ) (x: LogOrderOfMagnitude) : α • x = (x.exp ^ α).log := rfl

instance LogOrderOfMagnitude.posSMulStrictMono : PosSMulStrictMono ℝ LogOrderOfMagnitude := {
  elim := by
    intro α hα x y hxy
    simp only [smul_def, Additive.ofMul_symm_eq, Additive.ofMul_lt, ←power_vii' _ _ hα]
    convert Multiplicative.ofAdd_lt.mpr hxy
}

@[simp]
lemma OrderOfMagnitude.log_pow (X: OrderOfMagnitude) (α: ℝ): (X^α).log = α • X.log := rfl

abbrev internal (E : ℕ → Set ℝ) : Set Hyperreal := Filter.Germ.ofFun '' { (x : ℕ → ℝ) | ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), x n ∈ E n }

abbrev is_internal (E : Set Hyperreal) : Prop := ∃ E' : ℕ → Set ℝ, E = internal E'

lemma mem_internal (x: ℕ → ℝ) (E : ℕ → Set ℝ) : to_hyperreal x ∈ internal E ↔ ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), x n ∈ E n := by
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  . intro h
    obtain ⟨ y, hy, hxy ⟩ := h
    replace hxy : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), y n = x n := Quotient.exact hxy
    filter_upwards [hxy, hy] with n h hyE
    simp only [←h, hyE]
  intro h
  use x

lemma saturation (I : ℕ → Set Hyperreal) (hI : ∀ n, is_internal (I n)) (hI' : ∀ n, (I n).Nonempty) (hI'' : ∀ n, I (n+1) ⊆ I n): ∃ x : Hyperreal, ∀ n, x ∈ I n := by
  let f : Filter ℕ := Filter.hyperfilter ℕ
  let E := fun n ↦ (hI n).choose
  have hE (n:ℕ) : I n = internal (E n) := (hI n).choose_spec
  let F : ℕ → Set ℕ := fun n₀ ↦ {m:ℕ| m ≥ n₀ ∧ Nonempty (⋂ n ≤ n₀, E n m)}
  have hmono_I : Antitone I := antitone_nat_of_succ_le hI''

  have hnon (n₀:ℕ) : F n₀ ∈ f := by
    have hmem_I : ∃ x, ∀ n ≤ n₀, x ∈ I n := by
      use (hI' n₀).some
      intro n hn
      exact hmono_I hn (hI' n₀).some_mem
    set y : ℕ → ℝ := (to_hyperreal_surjective hmem_I.choose).choose
    have hy : ∀ᶠ m in f, ∀ n ∈ Finset.Iic n₀, y m ∈ E n m := by
      rw [Filter.eventually_all_finset]
      intro n hn
      rw [←mem_internal _ _, ← hE n]
      convert hmem_I.choose_spec n $ Finset.mem_Iic.mp hn
      exact (to_hyperreal_surjective hmem_I.choose).choose_spec
    have hlarge : ∀ᶠ m in f, m ≥ n₀ := (Nat.cofinite_eq_atTop ▸ Filter.hyperfilter_le_cofinite) $ Filter.Tendsto.eventually_ge_atTop (fun ⦃U⦄ a ↦ a) n₀
    filter_upwards [hy, hlarge] with m hm hm'
    simp only [ge_iff_le, nonempty_subtype, Set.mem_iInter, Set.mem_setOf_eq, hm', true_and, F]
    use y m
    intro n hn
    exact hm n (Finset.mem_Iic.mpr hn)
  let N : ℕ → ℕ := fun m ↦ sSup { n₀ : ℕ | m ∈ F n₀ }
  have hN (m:ℕ): Nonempty (⋂ n : Fin (N m), E n m) := by sorry
  let x : ℕ → ℝ := fun m ↦ (hN m).some
  use Filter.Germ.ofFun x
  intro n
  sorry

lemma Hyperreal.Ioi_internal (a b: Hyperreal) : ∃ E : ℕ → ℕ → Set ℝ, Set.Ioo a b = ⋂ n, internal (E n) := by
  sorry

lemma Hyperreal.completeness (a b: ℕ → Hyperreal) (ha: Monotone a) (hb: Antitone b) (hab: ∀ n, a n < b n) : ∃ x, ∀ n, a n < x ∧ x < b n := by
  sorry
