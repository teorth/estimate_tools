import Init.Core
import Mathlib.Order.Basic

-- It is important here that the preorder is not an instance, because sometimes we want to form the order quotient from a non-canonical preorder

def Preorder.toSetoid {α: Type*} (p: Preorder α) : Setoid α :=
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

lemma Preorder.equiv_iff {α: Type*} (p:Preorder α) (x y: α) :
  let _ := p.toSetoid
  x ≈ y ↔ x ≤ y ∧ y ≤ x := by convert Iff.rfl

def OrderQuotient {α:Type*} (p: Preorder α) := Quotient p.toSetoid

instance OrderQuotient.partialOrder {α:Type*} (p: Preorder α) : PartialOrder (OrderQuotient p) :=
{
  le := Quotient.lift₂ LE.le (by
    intro x₁ y₁ x₂ y₂ hx hy
    replace hx := (p.equiv_iff x₁ x₂).mp hx
    replace hy := (p.equiv_iff y₁ y₂).mp hy
    simp only [eq_iff_iff]
    exact ⟨ fun h ↦ hx.2.trans (h.trans hy.1), fun h ↦ hx.1.trans (h.trans hy.2) ⟩
  )
  lt := Quotient.lift₂ LT.lt (by
    intro x₁ y₁ x₂ y₂ hx hy
    replace hx := (p.equiv_iff x₁ x₂).mp hx
    replace hy := (p.equiv_iff y₁ y₂).mp hy
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
    exact Quotient.sound ((p.equiv_iff x y).mpr ⟨ h1, h2 ⟩)
}

def Preorder.quotient {α:Type*} (p: Preorder α) (x: α) : OrderQuotient p := Quotient.mk (p.toSetoid) x

lemma Preorder.quot_eq_iff {α:Type*} (p: Preorder α) (x y: α) : let _ := p.toSetoid
  Preorder.quotient p x = Preorder.quotient p y ↔ x ≈ y := by
  refine ⟨Quotient.exact, Quotient.sound ⟩

/-- for Mathlib? --/
lemma Quotient.liftBeta {α : Sort u} {s : Setoid α} {β : Sort v} (f : α → β) (c : ∀ (a b : α), a ≈ b → f a = f b) (a : α) : Quotient.lift f c (Quotient.mk s a) = f a := Quot.liftBeta f c _

/-- for Mathlib? --/
lemma Quotient.lift₂Beta {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ : Setoid α} {s₂ : Setoid β} (f : α → β → φ) (c : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) (a : α) (b : β) : Quotient.lift₂ f c (Quotient.mk s₁ a) (Quotient.mk s₂ b) = f a b := by
convert Quotient.liftBeta _ _ _

lemma Preorder.quot_le_iff {α:Type*} (p:Preorder α) (x y: α) : p.quotient x ≤ p.quotient y ↔ x ≤ y := by
  dsimp [Preorder.quotient, OrderQuotient.partialOrder]
  rw [Quotient.lift₂Beta]

lemma Preorder.quot_lt_iff {α:Type*} (p:Preorder α) (x y: α) : p.quotient x < p.quotient y ↔ x < y := by
  dsimp [Preorder.quotient, OrderQuotient.partialOrder]
  rw [Quotient.lift₂Beta]

open Classical in
noncomputable def Preorder.quot_linear {α:Type*} (p: Preorder α) (h: ∀ x y : α, x ≤ y ∨ y ≤ x) : LinearOrder (OrderQuotient p) :=
{
  le_total := by
    apply Quotient.ind; intro x
    apply Quotient.ind; intro y
    dsimp [Preorder.quotient, OrderQuotient.partialOrder]
    rw [Quotient.lift₂Beta]
    exact h x y

  toDecidableLE := by exact decRel LE.le
}
