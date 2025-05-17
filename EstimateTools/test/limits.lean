import Mathlib

/- In this file we are going to give some "epsilon-delta" proofs of facts about limits of functions on the real line. -/

/- First, we give the epsilon-delta definition of what it means for a function f : R -> R to converge to a limit L at a value x_0. -/

def limit (f : ℝ → ℝ) (L : ℝ) (x_0 : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x_0| < δ → |f x - L| < ε

/-- First we show that if a function f converges to a limit L at x_0, and a function g converges to a limit M at x_0, then f+g converge to L+M at x_0. -/

lemma limit_add (f g : ℝ → ℝ) (L M : ℝ) (x_0 : ℝ) :
  limit f L x_0 → limit g M x_0 → limit (fun x => f x + g x) (L + M) x_0 := by
  intro h1 h2 ε hε
  -- Use ε/2 for each function
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases h1 (ε / 2) hε2 with ⟨δ₁, hδ₁, h1'⟩
  rcases h2 (ε / 2) hε2 with ⟨δ₂, hδ₂, h2'⟩
  let δ := min δ₁ δ₂
  use δ
  constructor
  · exact lt_min hδ₁ hδ₂
  intro x hx
  have hx1 : |x - x_0| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : |x - x_0| < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)
  calc
    |(f x + g x) - (L + M)| = |(f x - L) + (g x - M)| := by rw [add_sub_add_comm]
    _ ≤ |f x - L| + |g x - M| := abs_add _ _
    _ < (ε / 2) + (ε / 2) := add_lt_add (h1' _ hx1) (h2' _ hx2)
    _ = ε := by ring

  /- A similar argument also works for differences of functions instead of sums. -/

lemma limit_sub (f g : ℝ → ℝ) (L M : ℝ) (x_0 : ℝ) :
  limit f L x_0 → limit g M x_0 → limit (fun x => f x - g x) (L - M) x_0 := by
  intro h1 h2 ε hε
  -- Use ε/2 for each function
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases h1 (ε / 2) hε2 with ⟨δ₁, hδ₁, h1'⟩
  rcases h2 (ε / 2) hε2 with ⟨δ₂, hδ₂, h2'⟩
  let δ := min δ₁ δ₂
  use δ
  constructor
  · exact lt_min hδ₁ hδ₂
  intro x hx
  have hx1 : |x - x_0| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : |x - x_0| < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)
  calc
    |(f x - g x) - (L - M)| = |(f x - L) - (g x - M)| := by
      congr 1
      abel
    _ ≤ |f x - L| + |g x - M| := abs_sub _ _
    _ < (ε / 2) + (ε / 2) := add_lt_add (h1' _ hx1) (h2' _ hx2)
    _ = ε := by ring

/-- Now let's try a trickier lemma where we work with products of functions rather than sums or differences. -/

lemma limit_mul (f g : ℝ → ℝ) (L M : ℝ) (x_0 : ℝ) :
  limit f L x_0 → limit g M x_0 → limit (fun x => f x * g x) (L * M) x_0 := by
  intro h1 h2 ε hε
  -- Use ε/(|L|+|M| + 1) for f and ε/(|L|+|M| + 1) for g
  have hε2 : 0 < ε / (|L|+|M| + 1) := by
    positivity
  have hε2' : 0 < min (ε / (|L|+|M| + 1)) 1 := by
    positivity
  rcases h1 (min (ε / (|L|+|M| + 1)) 1) hε2' with ⟨δ₁, hδ₁, h1'⟩
  have hε3 : 0 < ε / (|L|+|M| + 1) := by
    positivity
  rcases h2 (ε / (|L|+|M| + 1)) hε3 with ⟨δ₂, hδ₂, h2'⟩
  let δ := min δ₁ δ₂
  use δ
  constructor
  · exact lt_min hδ₁ hδ₂
  intro x hx
  have hx1 : |x - x_0| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : |x - x_0| < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have h1x_min : |f x - L| < min (ε / (|L|+|M| + 1)) 1 := h1' _ hx1
  have h1x : |f x - L| < ε / (|L|+|M| + 1) := lt_of_lt_of_le h1x_min (min_le_left _ _)
  have h1x' : |f x| < |L| + 1 := by
    calc
      |f x| = |(f x - L) + L| := by rw [sub_add_cancel (f x) L]
      _ ≤ |f x - L| + |L| := abs_add _ _
      _ < (min (ε / (|L|+|M| + 1)) 1) + |L| := by
        linarith
      _ ≤ 1 + |L| := by
        gcongr
        exact min_le_right _ _
      _ = |L| + 1 := by ring

  have h2x : |g x - M| < ε / (|L|+|M| + 1) := h2' _ hx2
  have h1x' : |f x| < |L| + ε / (|L|+|M| + 1) := by
    calc
      |f x| = |(f x - L) + L| := by rw [sub_add_cancel (f x) L]
      _ ≤ |f x - L| + |L| := abs_add _ _
      _ < ε / (|L|+|M| + 1) + |L| := by linarith
      _ = |L| + ε / (|L|+|M| + 1) := by ring
  have h2x' : |g x| < |M| + ε / (|L|+|M| + 1) := by
    calc
      |g x| = |(g x - M) + M| := by rw [sub_add_cancel (g x) M]
      _ ≤ |g x - M| + |M| := abs_add _ _
      _ < ε / (|L|+|M| + 1) + |M| := by linarith
      _ = |M| + ε / (|L|+|M| + 1) := by ring
  calc
    |(f x * g x) - (L * M)| = |(f x * g x) - (f x * M) + (f x * M) - (L * M)| := by
      congr
      abel
    _ = |f x * (g x - M) + M * (f x - L)| := by
      congr
      ring
    _ ≤ |f x * (g x - M)| + |M * (f x - L)| := abs_add _ _
    _ = |f x| * |g x - M| + |M| * |f x - L| := by
      rw [abs_mul, abs_mul]
    _ < (|L| + 1) * (ε / (|L| + |M| + 1)) + |M| * (ε / (|L| + |M| + 1)) := by
      refine add_lt_add_of_lt_of_le ?_ ?_
      · -- First term: |f x| * |g x - M| < (|L| + ε / (2 * |M| + 1)) * (ε / (2 * |L| + 1))
        gcongr
      · -- Second term: |M| * |f x - L| ≤ |M| * (ε / (|L| + |M| + 1))
        gcongr
    _ = ε := by
      calc
        (|L| + 1) * (ε / (|L| + |M| + 1)) + |M| * (ε / (|L| + |M| + 1))
          = ((|L| + 1) + |M|) * (ε / (|L| + |M| + 1)) := by ring
        _ = (|L| + |M| + 1) * (ε / (|L| + |M| + 1)) := by ring
        _ = ε := by
          have : |L| + |M| + 1 > 0 := by
            positivity
          field_simp [this]
