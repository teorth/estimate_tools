import Mathlib.Data.Real.Hyperreal

abbrev PositiveHyperreal := { x : Hyperreal // 0 < x }

instance PositiveHyperreal.lesssim : LE PositiveHyperreal :=
{
  le := fun X Y => ∃ C:ℝ, C > 0 ∧ (X : Hyperreal) ≤ C * Y
}

instance PositiveHyperreal.ll : LT PositiveHyperreal :=
{
  lt := fun X Y => ∀ ε:ℝ, ε>0 → (X : Hyperreal) ≤ ε * Y
}

instance PositiveHyperreal.preorder : Preorder PositiveHyperreal :=
{
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
