import Mathlib.Data.Real.Hyperreal
import EstimateTools.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

noncomputable instance Hyperreal.pow : Pow Hyperreal Hyperreal := ⟨ Filter.Germ.map₂ (fun x y => (Real.rpow x y)) ⟩
