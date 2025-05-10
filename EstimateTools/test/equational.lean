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

/- We denote $$S_z(x) = (xz)z$$ ...-/

abbrev S (z x : M) := (x ◇ z) ◇ z

/- ... and $$f(x,y) = xS_y(x) = x((xy)y)$$.-/

abbrev f (x y : M) := x ◇ (S y x)

lemma f_eq (x y : M) : f x y = x ◇ ((x ◇ y) ◇ y) := rfl

/-  The main equation is $$x=(yx)S_z(x)$$. -/

lemma main_eq (h: Equation1689 M) (x y z : M) : x = (y ◇ x) ◇ S z x := by
  exact h x y z

/- For $$x=S_b(a)$$ and $$y\in M a$$ we have $$yx=a$$. -/
lemma claim (h: Equation1689 M) (a b : M) (y : M) (hy : ∃ z, y = z ◇ a) : y ◇ S b a = a := by
  obtain ⟨z, rfl⟩ := hy
  exact Eq.rec (motive := fun a_1 t ↦ a_1 = a) (Eq.refl a) (h a z b)


/- **Lemma 1:** For any $$a,b,c$$, one has $$S_b(a) = a f(b,c)$$. -/
lemma Lemma1 (h:Equation1689 M) (a b c : M) : S b a = a ◇ (f b c) := by
-- *Proof:* For $$x=S_b(a)$$ and $$y\in M a$$ we have $$yx=a$$.
  set x := S b a
  have claim (y : M) (hy: ∃ z, y = z ◇ a) : y ◇ x = a := by
    exact claim h a b y hy

/- Then apply the main equation to these values of $$x,y$$ [Note: take y to be an arbitrary element of Ma, e.g. a ◇ a], to get [for any z] S_b(a) = aS_z(S_b(a)) -/
  have h1 (z:M) : S b a = a ◇ S z (S b a) := by
    set y := a ◇ a
    have hy : ∃ z, y = z ◇ a := by
      use a
    change x = a ◇ S z x
    have h2 : ∃ w, a = w ◇ x := by
      exact Exists.intro (b ◇ a) (h a b b)
    obtain ⟨w, hw⟩ := h2
    convert main_eq h _ w _

/- Then set $$z=S_c(b)$$ and note that $$S_b(a)z = ((ab)b)((bc)c) = b$$...
-/
  set z := S c b
  have h3 : S b a ◇ z = b := by
    exact Eq.rec (motive := fun a t ↦ a = b) (Eq.refl b) (h b (a ◇ b) c)
  calc
    S b a = a ◇ (((S b a) ◇ z) ◇ z) := by
      exact h1 z
    _ = a ◇ (b ◇ z) := by
      exact congrArg (Magma.op a) (congrFun (congrArg Magma.op h3) z)
    _ = a ◇ (f b c) := by
      exact rfl

/-  ... to simplify the right-hand side above and get, as announced,

S_b(a) = a((S_b(a)z)z) = a(bz) = a f(b,c). -/

/- **Lemma 2** For all $$a$$ there exists $$b,c,d$$ such that $$f(b,c)=S_d(a)$$.
-/
lemma Lemma2 (h:Equation1689 M) (a : M) : ∃ b c d, f b c = S d a := by
/- *Proof:* By definition of $$f$$ one has $$f(b,c)=bS_c(b)$$.-/
  have h1 (b c : M) : f b c = b ◇ S c b := by exact rfl

  set x := a
  set b := S x a
  use b
/-  Taking $$b=S_x(a)$$ for some $$x$$, -/

  have h2 (c : M) : b = a ◇ S c b := by
    unfold b
    have h3 : ∃ w, a = w ◇ S x a := by exact Exists.intro (a ◇ a) (h a a x)
    obtain ⟨w, hw⟩ := h3
    convert main_eq h _ w _

/- and rewriting $$b=aS_c(b)$$ using the first equation in the proof of Lemma 1 -/

/- we find f(b,c) = (aS_c(b))S_c(b)...
-/
  have h4 (c :M) : f b c = (a ◇ S c b) ◇ S c b := by
    rw [← h2]

/-
... which has the desired form for $$d=S_c(b)$$.  (Thus, the statement actually holds for all $$a,c$$.)
-/
  exact Exists.intro a (Exists.intro ((((a ◇ a) ◇ a) ◇ a) ◇ a) (h4 a))


/- **Lemma 3** For all $$a$$ there exists $$e$$ such that $$S_e(a) = a$$.
-/
lemma Lemma3 (h:Equation1689 M) (a : M) : ∃ e, S e a = a := by
  set a_2 := a ◇ a
  set a_3 := a_2 ◇ a

/- *Proof:* Left-multiply the equation in Lemma 1 by $$a^3=(a^2)a$$ to get (the first equality below comes from the main equation)

a = ((a^2)a)S_b(a) = a^3 (af(b,c)) .
-/
  have h1 ( b c : M ) : (a_2 ◇ a) ◇ S b a = a_3 ◇ (a ◇ f b c) := by
    congr
    exact Lemma1 h a b c

  have h1' (b c : M) : a = a_3 ◇ (a ◇ f b c) := by
    exact Eq.rec (motive := fun a_1 t ↦ a = a_1) (h a (a ◇ a) b) (h1 b c)

/-
Take $$b,c,d$$ as in Lemma 2... -/
  obtain ⟨b, c, d, h2⟩ := Lemma2 h a

/-  to rewrite $$af(b,c)=aS_d(a)=f(a,d)$$.-/
  have h3 : a ◇ f b c = a ◇ S d a := by
    exact congrArg (Magma.op a) h2

/- On the other hand, Lemma 1 with $$a=b$$ and $$c$$ replaced by $$d$$ implies $$a^3 = a f(a,d)$$ -/

  have h4: a_3 = a ◇ f a d := by
    exact Lemma1 h a a d

/-  so overall we get $$a=(af(a,d))f(a,d)$$... -/
  have h5 : a = (a ◇ f a d) ◇ f a d := by
    rw [← h4]
    exact Eq.rec (motive := fun a_1 t ↦ a = ((a ◇ a) ◇ a) ◇ a_1) (h1' b c) h3

/-  ...which is as desired for $$e=f(a,d)$$. -/
  exact Exists.intro (a ◇ ((a ◇ d) ◇ d)) (Eq.rec (motive := fun a_1 t ↦ a_1 = a) (Eq.refl a) h5)


 /-
*End of the proof:* For any $$a,y$$, using the notation $$e$$ from Lemma 3, the main equation gives $$a=(ya)S_e(a)=(ya)a=S_a(y)$$.
-/
theorem singleton_law (h:Equation1689 M) : Equation2 M := by
  have h1 (a y :M ): a = S a y := by
     obtain ⟨e, he⟩ := Lemma3 h a
     calc
       _ = (y ◇ a) ◇ S e a := by exact h a y e
       _ = (y ◇ a) ◇ a := by
         exact congrArg (Magma.op (y ◇ a)) he
       _ = S a y := by
        exact rfl
/-Inserting this back into the main equation gives $$(zy)a=y$$ for any $$a,y,z$$.-/
  have h2 (a y z : M) : (z ◇ y) ◇ a  = y := by
    symm
    have h3 : ∃ w, a = S w y := by exact Exists.intro a (h1 a y)
    obtain ⟨w, hw⟩ := h3
    convert main_eq h _ _ w

/- Thus $$ab=((da)c)b=c$$ for any $$a,b,c,d$$...-/
  have h3 (a b c d : M) : a ◇ b = c := by
    exact Eq.rec (motive := fun a_1 t ↦ a_1 ◇ b = c) (h2 b c (a ◇ a)) (h2 c a a)

  have h4 (a b c d : M) : a = d := by
    exact Eq.rec (motive := fun a_1 t ↦ a_1 = d) (h3 (a ◇ a) a d a) (h2 a a a)

  exact fun x y ↦ h4 x y y y
