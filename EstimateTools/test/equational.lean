import Mathlib.Tactic
import Canonical

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M: Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

abbrev Equation2 (M: Type _) [Magma M] := ∀ x y : M, x = y

variable {M : Type _} [Magma M]

/-
Human-readable proof that $x = (yx)((xz)z)$ (equation 1689) implies the singleton law (equation 2). -/

/-
We denote $$S_z(x) = (xz)z$$ and $$f(x,y) = xS_y(x) = x((xy)y)$$.-/

abbrev S (z:M) (x:M) : M := (x ◇ z) ◇ z
abbrev f (x y:M) : M := x ◇ S y x

lemma f_eq (x y:M) : f x y = x ◇ ((x ◇ y) ◇ y) := rfl



/-  The main equation is $$x=(yx)S_z(x)$$. -/

lemma main_eq (h: Equation1689 M) (x y z:M) : x = (y ◇ x) ◇ S z x := h x y z

lemma claim (h: Equation1689 M) (a b y:M) (hy: ∃ z:M, y = z ◇ a) : y ◇ (S b a) = a := by
  obtain ⟨z, rfl⟩ := hy
  exact Eq.rec (motive := fun a_1 t ↦ a_1 = a) (Eq.refl a) (h a z b)

/- **Lemma 1:** For any $$a,b,c$$, one has $$S_b(a) = a f(b,c)$$. -/

lemma Lemma_1 (h: Equation1689 M) (a b c:M) : S b a = a ◇ f b c := by
  set x := S b a
-- *Proof:* For $$x=S_b(a)$$ and $$y\in M a$$ we have $$yx=a$$.
  have claim (y:M)  (hy: ∃ z:M, y = z ◇ a): y ◇ x = a := by exact claim h a b y hy
/- Then apply the main equation to these values of $$x,y$$ [Note: take y to be an arbitrary element of Ma, e.g. a ◇ a], to get [for any z]
```math
S_b(a) = aS_z(S_b(a)) .
``` -/

  have h2 (z : M) : S b a = a ◇ S z (S b a) := by
    set y := a ◇ a
    have hy : ∃ z, y = z ◇ a := by
      use a
    exact
      Eq.rec (motive := fun a_1 t ↦ (a ◇ b) ◇ b = a_1 ◇ ((((a ◇ b) ◇ b) ◇ z) ◇ z))
        (h ((a ◇ b) ◇ b) (a ◇ a) z) (claim (a ◇ a) hy)

/- Then set $$z=S_c(b)$$ and note that $$S_b(a)z = ((ab)b)((bc)c) = b$$ to simplify the right-hand side above and get, as announced,
```math
S_b(a) = a((S_b(a)z)z) = a(bz) = a f(b,c) .
```
-/
  set z := S c b
  have h3 : S b a ◇ z = b := calc
    _ = ((a ◇ b) ◇ b) ◇ ((b ◇ c) ◇ c) := by
      exact Eq.refl (((a ◇ b) ◇ b) ◇ ((b ◇ c) ◇ c))
    _ = b := by
      exact Eq.symm (main_eq h b (a ◇ b) c)

  exact Eq.rec (motive := fun a_1 t ↦ (a ◇ b) ◇ b = a ◇ (a_1 ◇ ((b ◇ c) ◇ c))) (h2 ((b ◇ c) ◇ c)) h3


/- **Lemma 2** For all $$a$$ there exists $$b,c,d$$ such that $$f(b,c)=S_d(a)$$.
-/
lemma Lemma2 (h: Equation1689 M) (a:M) : ∃ b c d, f b c = S d a := by
/- *Proof:* By definition of $$f$$ one has $$f(b,c)=bS_c(b)$$.-/
  have h1 (b c :M) : f b c = b ◇ (S c b) := rfl
/-  Taking $$b=S_x(a)$$ for some $$x$$, -/
  set b := S a a
  use b
  set c := a
  use c
/- lemma claim (h: Equation1689 M) (a b y:M) (hy: ∃ z:M, y = z ◇ a) : y ◇ (S b a) = a := by
-/

  have h2 : b = a ◇ S c b := by
    convert (claim h _ _ _ ?_).symm
    exact Exists.intro (a ◇ a) (h a a a)

/- and rewriting $$b=aS_c(b)$$ using the first equation in the proof of Lemma 1, we find
```math
f(b,c) = (aS_c(b))S_c(b) ,
```
-/
  have h3 : f b c = (a ◇ S c b) ◇ S c b := by
    rw [h1]
    exact congrFun (congrArg Magma.op h2) (S c b)
/-
which has the desired form for $$d=S_c(b)$$.  (Thus, the statement actually holds for all $$a,c$$.)
-/
  exact Exists.intro ((((a ◇ a) ◇ a) ◇ a) ◇ a) h3

/- **Lemma 3** For all $$a$$ there exists $$e$$ such that $$S_e(a) = a$$.
-/

lemma Lemma3 (h:Equation1689 M) (a:M) : ∃ e, S e a = a := by
  let a_2 := a ◇ a
  let a_3 := a_2 ◇ a
/- *Proof:* Left-multiply the equation in Lemma 1 by $$a^3=(a^2)a$$ to get (the first equality below comes from the main equation)
```math
a = ((a^2)a)S_b(a) = a^3 (af(b,c)) .
```
-/
  have h1 (b c:M) : a = a_3 ◇ (a ◇ f b c) := calc
    a = (a_2 ◇ a) ◇ S b a := by
      exact h a a_2 b
    _ = _ := by
      congr
      exact Lemma_1 h a b c
/-
Take $$b,c,d$$ as in Lemma 2 to rewrite $$af(b,c)=aS_d(a)=f(a,d)$$.
-/
  obtain ⟨ b,c,d, lemma2 ⟩ := Lemma2 h a

  have h2 : a ◇ f b c = f a d := calc
    _ = a ◇ S d a := by exact congrArg (Magma.op a) lemma2
    _ = f a d := by exact rfl

/- On the other hand, Lemma 1 with $$a=b$$ and $$c$$ replaced by $$d$$ implies $$a^3 = a f(a,d)$$ -/
  have h3 : a_3 = a ◇ f a d := by exact Lemma_1 h a a d

/-  so overall we get $$a=(af(a,d))f(a,d)$$, which is as desired for $$e=f(a,d)$$. -/
  have h4 : a= (a ◇ f a d) ◇ f a d := by
    rw [←h3]
    exact Eq.rec (motive := fun a_1 t ↦ a = ((a ◇ a) ◇ a) ◇ a_1) (h1 b c) h2

  exact Exists.intro (a ◇ ((a ◇ d) ◇ d)) (Eq.rec (motive := fun a_1 t ↦ a_1 = a) (Eq.refl a) h4)


theorem main (h : Equation1689 M) : Equation2 M := by
 /-
*End of the proof:* For any $$a,y$$, using the notation $$e$$ from Lemma 3, the main equation gives $$a=(ya)S_e(a)=(ya)a=S_a(y)$$.
-/
  have h1 (a y : M) : a = S a y := by
    obtain ⟨ e, he ⟩ := Lemma3 h a
    calc
      a =(y ◇ a) ◇ S e a := by exact h a y e
      _ = (y ◇ a) ◇ a := by
        exact congrArg (Magma.op (y ◇ a)) he
      _ = S a y := by exact rfl
/-Inserting this back into the main equation gives $$(zy)a=y$$ for any $$a,y,z$$.-/
  have h2 (a y z:M) : (z ◇ y) ◇ a = y := by
    symm
    convert main_eq h _ _ a
    exact h1 a y

/- Thus $$ab=((da)c)b=c$$ for any $$a,b,c,d$$, thus $$a=bc=d$$ for any $$a,b,c,d$$.-/
  have h3 (a b c d:M) : a ◇ b = c := calc
    a ◇ b = ((d ◇ a) ◇ c) ◇ b := by
      exact
        Eq.rec (motive := fun a_1 t ↦ a_1 ◇ b = ((d ◇ a) ◇ c) ◇ b) (Eq.refl (((d ◇ a) ◇ c) ◇ b))
          (h2 c a d)
    _ = c := by exact h2 b c (d ◇ a)

  exact fun x y ↦ Eq.rec (motive := fun a t ↦ a = y) (h3 (y ◇ x) y y y) (h2 y x y)


````
-/
