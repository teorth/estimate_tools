import Init.Core
import Mathlib.Order.Basic


-- it may possibly be inadvisable to automatically give every preorder a setoid structure; happy to take suggestions for alternatives

instance Preorder.toSetoid {α: Type*} [Preorder α] : Setoid α :=
{
  r := fun x y => x ≤ y ∧ y ≤ x
  iseqv := {
    refl := by
      simp only [_root_.le_refl, and_self, implies_true]
    symm := by
      intro x y ⟨ h1, h2 ⟩
      exact ⟨ h2, h1 ⟩
    trans := by
      intro x y z ⟨ h1, h2 ⟩ ⟨ h3, h4 ⟩
      exact ⟨ h1.trans h3, h4.trans h2 ⟩
  }
}

lemma Preorder.equiv_iff {α: Type*} [Preorder α] (x y: α) : x ≈ y ↔ x ≤ y ∧ y ≤ x :=
  Iff.rfl

def OrderQuotient (α:Type*) [h: Preorder α] := Quotient h.toSetoid

instance OrderQuotient.partialOrder (α:Type*) [h: Preorder α] : PartialOrder (OrderQuotient α) :=
{
  le := Quotient.lift₂ LE.le (by
    intro x₁ y₁ x₂ y₂ hx hy
    rw [Preorder.equiv_iff] at hx hy
    simp only [eq_iff_iff]
    exact ⟨ fun h ↦ hx.2.trans (h.trans hy.1), fun h ↦ hx.1.trans (h.trans hy.2) ⟩
  )
  lt := Quotient.lift₂ LT.lt (by
    intro x₁ y₁ x₂ y₂ hx hy
    rw [Preorder.equiv_iff] at hx hy
    simp only [eq_iff_iff]
    exact ⟨ fun h ↦ lt_of_lt_of_le (lt_of_le_of_lt hx.2 h) hy.1, fun h ↦ lt_of_lt_of_le (lt_of_le_of_lt hx.1 h) hy.2 ⟩
  )
  le_refl := by
    apply Quot.ind; intro x
    simp
  le_trans := by
    apply Quot.ind; intro x
    apply Quot.ind; intro y
    apply Quot.ind; intro z
    simp
    exact Preorder.le_trans x y z
  lt_iff_le_not_le := by
    apply Quot.ind; intro x
    apply Quot.ind; intro y
    simp
    exact lt_iff_le_not_le
  le_antisymm := by
    apply Quot.ind; intro x
    apply Quot.ind; intro y
    simp
    intro h1 h2
    exact Quotient.sound ((Preorder.equiv_iff x y).mpr ⟨ h1, h2 ⟩)
}
