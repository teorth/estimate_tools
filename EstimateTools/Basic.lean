import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Real.Basic
import EstimateTools.OrderOfMagnitude

example (x y z:LogOrderOfMagnitude) (h1: x ≤ 2 • y) (h2: y ≤ z) : x ≤ 2 • z := calc
  x ≤ 2 • y := h1
  _ ≤ 2 • z := by
    simp only [←Nat.cast_smul_eq_nsmul ℝ _ _]
    apply smul_le_smul_of_nonneg_left h2
    norm_num
