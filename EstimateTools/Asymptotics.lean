import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import EstimateTools.Order

-- Class of functions on a parameter space Ω equipped with a filter that are eventually positive.

class EventuallyPositive {Ω:Type*} (f: Filter Ω) where
  val : Ω → ℝ
  pos : ∀ᶠ N in f, val N > 0

instance EventuallyPositive.lesssim {Ω:Type*} (f: Filter Ω) : Preorder (EventuallyPositive f) :=
{
  le := fun X Y => ∃ (C:ℝ), C > 0 ∧ ∀ᶠ N in f, X.val N ≤ C * Y.val N
  lt := fun X Y => ∀ (ε:ℝ), ε>0 → ∀ᶠ N in f, X.val N ≤ ε * Y.val N
  le_refl := by
    intro X; use 1
    simp
  le_trans := by
    intro X Y Z ⟨ C1, hC1, h1 ⟩ ⟨ C2, hC2, h2 ⟩
    use C1 * C2
    refine ⟨ Left.mul_pos hC1 hC2, ?_ ⟩
    have := Y.pos
    filter_upwards [h1, h2, this] with N h1 h2 this
    calc
      _ ≤ C1 * Y.val N := h1
      _ ≤ C1 * (C2 * Z.val N) := by gcongr
      _ = (C1 * C2) * Z.val N := by rw [mul_assoc]
  lt_iff_le_not_le := by
    intro X Y
    constructor
    . intro h
      constructor
      . use 1
        simp only [zero_lt_one, h 1, true_and]
      by_contra! this
      obtain ⟨ C, hC, this ⟩ := this
      have hC_inv : C⁻¹ > 0 := Right.inv_pos.mpr hC
      replace h := h C⁻¹ hC_inv
      have hfalse := ∀ᶠ N in f, False := by
        have hY := Y.pos
        sorry
      sorry

    sorry
}

instance EventuallyPositive.distrib {Ω:Type*} (f: Filter Ω) : Distrib (EventuallyPositive f) :=
{
  add := fun X Y => {
    val := fun N => X.val N + Y.val N
    pos := by sorry
  }
  mul := fun X Y => {
    val := fun N => X.val N * Y.val N
    pos := by sorry
  }
  left_distrib := by sorry
  right_distrib := by sorry
}

def OrderOfMagnitude {Ω:Type*} (f: Filter Ω) := OrderQuotient (EventuallyPositive f)
