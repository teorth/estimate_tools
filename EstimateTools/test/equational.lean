import Mathlib.Tactic
import Canonical

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (G: Type _) [Magma G] := ∀ x y z : G, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

abbrev Equation2 (G: Type _) [Magma G] := ∀ x y : G, x = y

variable {G : Type _} [Magma G]

/-
Human-readable proof that $x = (yx)((xz)z)$ (equation 1689) implies the singleton law (equation 2). -/

/-
We denote $$S_z(x) = (xz)z$$ and $$f(x,y) = xS_y(x) = x((xy)y)$$.-/

/-  The main equation is $$x=(yx)S_z(x)$$. -/


/- **Lemma 1:** For any $$a,b,c$$, one has $$S_b(a) = a f(b,c)$$. -/

/-
*Proof:* For $$x=S_b(a)$$ and $$y\in Ma$$ we have $$yx=a$$. -/

/- Then apply the main equation to these values of $$x,y$$ to get
```math
S_b(a) = aS_z(S_b(a)) .
``` -/

/- Then set $$z=S_c(b)$$ and note that $$S_b(a)z = ((ab)b)((bc)c) = b$$ to simplify the right-hand side above and get, as announced,
```math
S_b(a) = a((S_b(a)z)z) = a(bz) = a f(b,c) .
```
-/


/- **Lemma 2** For all $$a$$ there exists $$b,c,d$$ such that $$f(b,c)=S_d(a)$$.
-/

/- *Proof:* By definition of $$f$$ one has $$f(b,c)=bS_c(b)$$.-/

/-  Taking $$b=S_x(a)$$ for some $$x$$,
and rewriting $$b=aS_c(b)$$ using the first equation in the proof of Lemma 1, we find
```math
f(b,c) = (aS_c(b))S_c(b) ,
```
-/

/-
which has the desired form for $$d=S_c(b)$$.  (Thus, the statement actually holds for all $$a,c$$.)
-/

/- **Lemma 3** For all $$a$$ there exists $$e$$ such that $$S_e(a) = a$$.
-/

/- *Proof:* Left-multiply the equation in Lemma 1 by $$a^3=(a^2)a$$ to get (the first equality below comes from the main equation)
```math
a = ((a^2)a)S_b(a) = a^3 (af(b,c)) .
```
-/

/-
Take $$b,c,d$$ as in Lemma 2 to rewrite $$af(b,c)=aS_d(a)=f(a,d)$$.
-/

/- On the other hand, Lemma 1 with $$a=b$$ and $$c$$ replaced by $$d$$ implies $$a^3 = a f(a,d)$$ -/

/-  so overall we get $$a=(af(a,d))f(a,d)$$, which is as desired for $$e=f(a,d)$$. -/

/-
*End of the proof:* For any $$a,y$$, using the notation $$e$$ from Lemma 3, the main equation gives $$a=(ya)S_e(a)=(ya)a=S_a(y)$$.
-/

/-Inserting this back into the main equation gives $$(zy)a=y$$ for any $$a,y,z$$.-/

/- Thus $$ab=((da)c)b=c$$ for any $$a,b,c,d$$, thus $$a=bc=d$$ for any $$a,b,c,d$$.
````
-/
