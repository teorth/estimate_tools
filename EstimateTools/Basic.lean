import Mathlib.Algebra.Order.Module.Defs

variable (R:Type*) [AddCommMonoid R] [Module ℝ R] [LinearOrder R] [PosSMulStrictMono R ℝ]

example (x y z:ℝ) (h1: x ≤ 2 • y) (h2: y ≤ z) : x ≤ 2 • z := calc
  x ≤ 2 • y := h1
  _ ≤ 2 • z := by
    simp only [←Nat.cast_smul_eq_nsmul]
    apply smul_le_smul_of_nonneg_left
    
