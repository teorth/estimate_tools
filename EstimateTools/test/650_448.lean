import Mathlib.Tactic
import Canonical

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation650 (G: Type _) [Magma G] := ∀ x y z : G, x = x ◇ (y ◇ ((z ◇ x) ◇ y))

abbrev Equation448 (G: Type _) [Magma G] := ∀ x y z : G, x = x ◇ (y ◇ (z ◇ (x ◇ z)))

theorem Equation650_implies_Equation448 (G : Type*) [Magma G] (h : Equation650 G) : Equation448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 :=
    by exact Eq.rec (motive := fun a t ↦ a = X0) (Eq.refl X0) (h X0 X1 X2)
  have eq10 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) :=
    by exact fun a ↦ nh a
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) :=
    by sorry
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 :=
    by exact
      Eq.rec (motive := fun a t ↦ X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ a) = X1)
        (eq9 X1 (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) X0) (eq9 (X0 ◇ X1) X2 X3)
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X2 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) :=
    by sorry
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) :=
    by sorry
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) :=
    by sorry
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) = ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) :=
    by sorry
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) :=
    by sorry
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 :=
    by sorry
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) :=
    by sorry
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) :=
  superpose eq11 eq12 -- superposition 12,11, 11 into 12, unify on (0).2 in 11 and (0).1.2.1.2.1.2 in 12
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq21 -- superposition 21,11, 11 into 21, unify on (0).2 in 11 and (0).2.2.2 in 21
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq11 eq36 -- superposition 36,11, 11 into 36, unify on (0).2 in 11 and (0).2.2.1.2 in 36
  have eq372 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq55 eq12 -- superposition 12,55, 55 into 12, unify on (0).2 in 55 and (0).1.2.1.2 in 12
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := superpose eq23 eq271 -- superposition 271,23, 23 into 271, unify on (0).2 in 23 and (0).2.2.1 in 271
  have eq1434 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) = ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq23 eq55 -- superposition 55,23, 23 into 55, unify on (0).2 in 23 and (0).2.2 in 55
  have eq1436 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3))) = X3 := superpose eq23 eq33 -- superposition 33,23, 23 into 33, unify on (0).2 in 23 and (0).1.2.1 in 33
  have eq1518 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq1434 eq1433 -- backward demodulation 1433,1434
  have eq1578 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq13 eq37 -- superposition 37,13, 13 into 37, unify on (0).2 in 13 and (0).2.2.1.2.1 in 37
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := superpose eq36 eq37 -- superposition 37,36, 36 into 37, unify on (0).2 in 36 and (0).2.2.1.2.1 in 37
  have eq1693 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq11 eq1578 -- forward demodulation 1578,11
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := superpose eq11 eq1579 -- forward demodulation 1579,11
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq31 eq1695 -- superposition 1695,31, 31 into 1695, unify on (0).2 in 31 and (0).2.2.2 in 1695
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1695 eq9 -- superposition 9,1695, 1695 into 9, unify on (0).2 in 1695 and (0).1.2.2 in 9
  have eq1883 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose eq1695 eq12 -- superposition 12,1695, 1695 into 12, unify on (0).2 in 1695 and (0).1.2.1.2 in 12
  have eq2683 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1693 eq12 -- superposition 12,1693, 1693 into 12, unify on (0).2 in 1693 and (0).1.2.1.2 in 12
  have eq2688 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq31 eq1878 -- superposition 1878,31, 31 into 1878, unify on (0).2 in 31 and (0).2.2.1.2 in 1878
  have eq2760 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq31 eq1883 -- superposition 1883,31, 31 into 1883, unify on (0).2 in 31 and (0).1.2.1.1.2 in 1883
  have eq2846 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq11 eq1436 -- superposition 1436,11, 11 into 1436, unify on (0).2 in 11 and (0).1.2.1.2 in 1436
  have eq2902 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := superpose eq21 eq1518 -- superposition 1518,21, 21 into 1518, unify on (0).2 in 21 and (0).1 in 1518
  have eq3015 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq2902 eq2760 -- backward demodulation 2760,2902
  have eq3016 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2902 eq2688 -- backward demodulation 2688,2902
  have eq3017 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq2902 eq1874 -- backward demodulation 1874,2902
  have eq3019 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq3015 -- forward demodulation 3015,11
  have eq3020 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq3016 -- forward demodulation 3016,11
  have eq3027 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3))) = X3 := superpose eq3017 eq2846 -- backward demodulation 2846,3017
  have eq3160 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq3020 eq3019 -- superposition 3019,3020, 3020 into 3019, unify on (0).2 in 3020 and (0).1.2 in 3019
  have eq3180 (X0 X2 : G) : (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := superpose eq3020 eq372 -- superposition 372,3020, 3020 into 372, unify on (0).2 in 3020 and (0).1.2.1.1 in 372
  have eq3226 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq3020 eq30 -- superposition 30,3020, 3020 into 30, unify on (0).2 in 3020 and (0).1.2.1 in 30
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := superpose eq3160 eq3027 -- backward demodulation 3027,3160
  have eq3252 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq3017 eq3226 -- forward demodulation 3226,3017
  have eq3255 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3252 eq2683 -- backward demodulation 2683,3252
  have eq3300 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3250 eq55 -- superposition 55,3250, 3250 into 55, unify on (0).2 in 3250 and (0).2.2 in 55
  have eq3301 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq3250 eq271 -- superposition 271,3250, 3250 into 271, unify on (0).2 in 3250 and (0).2.2.1 in 271
  have eq3310 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X2 := superpose eq3300 eq3180 -- backward demodulation 3180,3300
  have eq3312 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3300 eq3301 -- forward demodulation 3301,3300
  have eq3326 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq3312 eq3255 -- backward demodulation 3255,3312
  have eq3413 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq33 -- superposition 33,3312, 3312 into 33, unify on (0).2 in 3312 and (0).1.2.1 in 33
  have eq3457 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq3312 eq9 -- superposition 9,3312, 3312 into 9, unify on (0).2 in 3312 and (0).1.2 in 9
  have eq3534 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X2))) := superpose eq3312 eq21 -- superposition 21,3312, 3312 into 21, unify on (0).2 in 3312 and (0).1 in 21
  have eq3590 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq3312 eq3413 -- forward demodulation 3413,3312
  have eq3656 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq3312 eq3457 -- superposition 3457,3312, 3312 into 3457, unify on (0).2 in 3312 and (0).1.2 in 3457
  have eq3685 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq3457 eq3312 -- superposition 3312,3457, 3457 into 3312, unify on (0).2 in 3457 and (0).1 in 3312
  have eq3867 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq3656 eq3310 -- backward demodulation 3310,3656
  have eq4044 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) := superpose eq3867 eq11 -- superposition 11,3867, 3867 into 11, unify on (0).2 in 3867 and (0).1.2.1 in 11
  have eq4123 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq3867 eq3685 -- superposition 3685,3867, 3867 into 3685, unify on (0).2 in 3867 and (0).1.2.2 in 3685
  have eq4159 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq4123 eq4044 -- backward demodulation 4044,4123
  have eq4714 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) := superpose eq4159 eq3534 -- backward demodulation 3534,4159
  have eq5273 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := superpose eq4159 eq3326 -- backward demodulation 3326,4159
  have eq5819 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq5273 eq4714 -- backward demodulation 4714,5273
  have eq5851 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq5819 eq3590 -- backward demodulation 3590,5819
  have eq5870 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq3656 eq5851 -- forward demodulation 5851,3656
  have eq5878 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq5870 eq3685 -- backward demodulation 3685,5870
  have eq5892 : sK0 ≠ (sK0 ◇ sK1) := superpose eq5870 eq10 -- backward demodulation 10,5870
  subsumption eq5892 eq5878
