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

/- We denote $y^0=y$ and $y^{n+1}=y^n\op y$ for $n\geq 0$.  This is shifted by 1 from the usual definition of power -/

def power (y : M) : Nat → M
  | 0 => y
  | n+1 => power y n ◇ y

notation:100 x "^" n => power x n

abbrev square (x:M) := power x 1
abbrev cube (x:M) := power x 2
abbrev fourth (x:M) := power x 3
abbrev fifth (x:M) := power x 4
abbrev sixth (x:M) := power x 5

/- We also introduce the notation $f(x,y) = (x \op y) \op y$ -/

abbrev f (x y : M) := (x ◇ y) ◇ y

/- and $g(x,y) = x\op f(x,y) = x \op ((x \op y) \op y)$. -/

abbrev g (x y : M) := x ◇ f x y

lemma g_eq (x y : M) : g x y = x ◇ ((x ◇ y) ◇ y) := rfl

/- The initial equation states $x = (y \op x) \op f(x,z)$. -/

lemma initial_eq (h: Equation1689 M) (x y z : M) : x = (y ◇ x) ◇ f x z := by
  exact h x y z

/- For any $t,u,v \in M$, the combinations $x = f(t,u)$ and $y = v \op t$ obey $y \op x = t$. -/

lemma y_x_eq_t (h: Equation1689 M) (t u v : M) : (v ◇ t) ◇ f t u = t := by
  have h1 : f t u = (t ◇ u) ◇ u := rfl
  convert (initial_eq h t v u).symm


/- Inserting these values into the initial equation yields the identity
$f(t,u) = t \op f(f(t,u),z)$. -/

lemma eq_xtSzx (h: Equation1689 M) (t u z : M) : f t u = t ◇ f (f t u) z := by
  set x := f t u
  set y := u ◇ t -- Actually v ◇ t for some v, but we only need y ◇ x = t
  have hyx : y ◇ x = t := by
    exact y_x_eq_t h t u u
  calc
    f t u = (y ◇ x) ◇ f x z := by
      convert h x y z
    _ = t ◇ f (f t u) z := by
      rw [hyx]

/- Specialize to $z=f(u,v)$ and note that $f(t,u) \op z = (\cdots \op u) \op f(u,v) = u$
by the initial equation -/

lemma f_t_u_z_eq_u (h: Equation1689 M) (t u v : M) : f t u ◇ f u v = u := by
  have h1 : f t u = (t ◇ u) ◇ u := rfl
  have h2 : f u v = (u ◇ v) ◇ v := rfl
  convert (initial_eq h u (t ◇ u) v).symm

/- so that $f(f(t,u),z) = (f(t,u) \op z) \op z = u \op z = g(u,v)$. -/

lemma f_f_t_u_z_eq_g_u_v (h: Equation1689 M) (t u v : M) : f (f t u) (f u v) = g u v := by
  calc
    f (f t u) (f u v) = (f t u ◇ f u v) ◇ f u v := rfl
    _ = u ◇ f u v := by
      rw [f_t_u_z_eq_u h t u v]
    _ = g u v := rfl

/- Inserting this into \eqref{Kisielewicz-xtSzx} yields $f(t,u) = t \op g(u,v)$. -/

lemma eq_tech (h: Equation1689 M) (t u v : M) : f t u = t ◇ g u v := by
  have h1 := eq_xtSzx h t u (f u v)
  calc
    f t u = t ◇ f (f t u) (f u v) := by
      exact h1
    _ = t ◇ g u v := by
      rw [f_f_t_u_z_eq_g_u_v h t u v]

/- On the one hand, \eqref{Kisielewicz-xtSzx} with $z=u=t$ states that $(cube t) = t \op (fifth t)$ -/

lemma t_cubed_eq_t_t5 (h: Equation1689 M) (t : M) : (cube t) = t ◇ (fifth t) := by
  have h1 := eq_xtSzx h t t t
  have h_t3 : f t t = (cube t) := by
    calc
      f t t = (t ◇ t) ◇ t := rfl
      _ = (square t) ◇ t := rfl
      _ = (cube t) := rfl
  have h_t5 : f (cube t) t = (fifth t) := by
    calc
      f (cube t) t = ((cube t) ◇ t) ◇ t := rfl
      _ = (fourth t) ◇ t := rfl
      _ = (fifth t) := rfl
  rw [h_t3, h_t5] at h1
  exact h1

/- so (using $f(t^n,t)=t^{n+2}$) -/

lemma f_tn_t (t : M) (n : Nat) : f (power t n) t = power t (n+2) := by
  calc
    f (power t n) t = (power t n ◇ t) ◇ t := rfl
    _ = power t (n+1) ◇ t := rfl
    _ = power t (n+2) := rfl

/- $f(t,(fifth t)) = (t \op (fifth t)) \op (fifth t) = (cube t) \op (fifth t) = (cube t) \op f((cube t),t) = g((cube t),t)$ -/

lemma f_t_t5_eq_g_t3_t (h: Equation1689 M) (t : M) : f t ((fifth t)) = g (cube t) t := by
  calc
    f t ((fifth t)) = (t ◇ (fifth t)) ◇ (fifth t) := rfl
    _ = (cube t) ◇ (fifth t) := by
      rw [t_cubed_eq_t_t5 h t]
    _ = (cube t) ◇ f (cube t) t := by
      rw [f_tn_t t 2]
    _ = g (cube t) t := rfl

/- and \eqref{Kisielewicz-tech} with $(u,v)=((cube t),t)$ then implies
$f(t,(cube t)) = t \op g((cube t),t) = t \op f(t,(fifth t)) = g(t,(fifth t))$. -/

lemma f_t_t3_eq_g_t_t5 (h: Equation1689 M) (t : M) : f t ((cube t)) = g t ((fifth t)) := by
  have h1 := eq_tech h t (cube t) t
  calc
    f t ((cube t)) = t ◇ g (cube t) t := by
      exact h1
    _ = t ◇ f t ((fifth t)) := by
      rw [← f_t_t5_eq_g_t3_t h t]
    _ = g t ((fifth t)) := rfl

/- On the other hand, \eqref{Kisielewicz-tech} with $(u,v)=(t,(fifth t))$ implies $(cube t) = t \op g(t,(fifth t))$. -/

lemma t3_eq_t_g_t_t5 (h: Equation1689 M) (t : M) : (cube t) = t ◇ g t ((fifth t)) := by
  have h1 := eq_tech h t t (fifth t)
  have h_t3 : f t t = (cube t) := by
    calc
      f t t = (t ◇ t) ◇ t := rfl
      _ = (square t) ◇ t := rfl
      _ = (cube t) := rfl
  rw [h_t3] at h1
  exact h1

/- We deduce
$f(t,g(t,(fifth t))) = (t \op g(t,(fifth t))) \op g(t,(fifth t)) = (cube t) \op f(t, (cube t)) = (\cdots \op t) \op f(t,\dots) = t$. -/

lemma f_t_g_t_t5_eq_t (h: Equation1689 M) (t : M) : f t (g t ((fifth t))) = t := by
  calc
    f t (g t ((fifth t))) = (t ◇ g t ((fifth t))) ◇ g t ((fifth t)) := rfl
    _ = (cube t) ◇ g t ((fifth t)) := by
      rw [t3_eq_t_g_t_t5 h t]
    _ = (cube t) ◇ f t ((cube t)) := by
      rw [← f_t_t3_eq_g_t_t5 h t]
    _ = ((square t) ◇ t) ◇ f t ((cube t)) := rfl
    _ = t := by
      convert (initial_eq h t (square t) ((cube t))).symm

/- Our main step will be to prove that for all $t\in M$ there exists $w\in M$ such that $f(t,w) = t$.
The rest of the proof is then straightforward. -/

lemma f_t_w_eq_t (h: Equation1689 M) (t : M) : ∃ w, f t w = t := by
  /- We proved above that $w = g(t,(fifth t)) = t \op t^7$ works -/
  use g t ((fifth t))
  exact f_t_g_t_t5_eq_t h t

/- Indeed, the initial equation gives
$t = (y \op t) \op f(t,w) = (y \op t) \op t = f(y,t)$ for any $t,y\in M$. -/

lemma t_eq_f_y_t (h: Equation1689 M) (t y : M) : t = f y t := by
  obtain ⟨w, hw⟩ := f_t_w_eq_t h t
  calc
    t = (y ◇ t) ◇ f t w := by
      exact initial_eq h t y w
    _ = (y ◇ t) ◇ t := by
      rw [hw]
    _ = f y t := rfl

/- With such a simple expression of $f$ the initial equation becomes $x = (y \op x) \op z$ -/

lemma simplified_eq (h: Equation1689 M) (x y z : M) : x = (y ◇ x) ◇ z := by
  have h1 := initial_eq h x y z
  have h2 : f x z = z := by
    exact (t_eq_f_y_t h z x).symm
  rw [h2] at h1
  exact h1

/- which easily implies the singleton law, for instance by writing
$x = ((y \op w) \op x) \op z = w \op z$ for any $w,x,y,z \in M$. -/

theorem singleton_law (h: Equation1689 M) : Equation2 M := by
  have h1 (w x y z : M) : x = w ◇ z := by
    calc
      x = ((y ◇ w) ◇ x) ◇ z := by
        exact simplified_eq h x (y ◇ w) z
      _ = w ◇ z := by
        congr
        convert (simplified_eq h w y x).symm

  exact fun x y ↦
    Eq.rec (motive := fun a t ↦ x = a) (h1 y x y y)
      (Eq.rec (motive := fun a t ↦ a = y) (Eq.refl y) (h1 y y y y))
