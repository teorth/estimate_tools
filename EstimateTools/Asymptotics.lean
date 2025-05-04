import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import EstimateTools.Order

-- Class of functions on a parameter space Ω equipped with a filter that are eventually positive.

class EventuallyPositive {Ω:Type*} (f: Filter Ω) where
  val : Ω → ℝ
  pos : ∀ᶠ N in f, val N > 0

instance EventuallyPositive.LE {Ω:Type*} (f: Filter Ω) : LE (EventuallyPositive f) :=
{
  le := fun X Y => ∃ (C:ℝ), C > 0 ∧ ∀ᶠ N in f, X.val N ≤ C * Y.val N
}

instance EventuallyPositive.lesssim {Ω:Type*} (f: Filter Ω) : Preorder (EventuallyPositive f) :=
{
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

  lt := fun X Y => (X ≤ Y) ∧ ¬ (Y ≤ X)
  lt_iff_le_not_le := by
    intro X Y
    rfl
}

instance EventuallyPositive.add {Ω:Type*} (f: Filter Ω) : Add (EventuallyPositive f) :=
{
  add := fun X Y => {
    val := fun N => X.val N + Y.val N
    pos := by sorry
  }
}


def OrderOfMagnitude {Ω:Type*} (f: Filter Ω) := OrderQuotient (EventuallyPositive f)
