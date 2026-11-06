module

public import Cylinder.CurvePolarLocal
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.MvPolynomial.Rename

/-! Homogeneous evaluation into arbitrary commutative target rings,
including the actual torus localization. Dividing the coordinates by
a unit gives the literal projective change-of-chart formula. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.HomogeneousTorusRescaling

open MvPolynomial Cylinder.CurvePolarLocal

set_option autoImplicit false

variable {K A σ : Type*} [CommRing K] [CommRing A] [Fintype σ]

theorem homogeneous_eval₂_mul (f : K →+* A) (H : MvPolynomial σ K) (m : ℕ)
    (hH : H.IsHomogeneous m) (u : A) (x : σ → A) :
    eval₂ f (fun i => u * x i) H = u ^ m * eval₂ f x H := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have hdegree : β.degree = m := by
    by_contra hdegree
    exact (MvPolynomial.mem_support_iff.mp hβ) (hH.coeff_eq_zero hdegree)
  have hsum : (∑ i : σ, β i) = m := (Finsupp.degree_eq_sum β).symm.trans hdegree
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hsum]
  ring

section Plane

variable {K : Type*} [Field K] {A : Type*} [CommRing A]

theorem eval₂_dehomogenize (f : K →+* A) (x : Fin 2 → A)
    (H : HomogeneousPlanePolynomial (K := K)) :
    eval₂ f x (dehomogenize H) = eval₂ f (fun i => i.elim 1 x) H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add H G hH hG => simp [hH, hG]
  | mul_X H i hH =>
    cases i <;> simp [hH]

theorem normalized_chart_eval (f : K →+* A)
    (H : HomogeneousPlanePolynomial (K := K)) (m : ℕ) (hH : H.IsHomogeneous m)
    (i : Option (Fin 2)) (x : Option (Fin 2) → A) (u : Aˣ) (hu : (u : A) = x i) :
    eval₂ f (fun j => ((u⁻¹ : Aˣ) : A) * x (Equiv.swap i none (some j)))
      (dehomogenize (MvPolynomial.rename (Equiv.swap i none) H)) =
        ((u⁻¹ : Aˣ) : A) ^ m * eval₂ f x H := by
  let e := Equiv.swap i none
  have hnorm :
      (fun j : Option (Fin 2) => ((u⁻¹ : Aˣ) : A) * x (e j)) =
        (fun j => j.elim 1 (fun k => ((u⁻¹ : Aˣ) : A) * x (e (some k)))) := by
    funext j
    cases j with
    | none =>
      change ((u⁻¹ : Aˣ) : A) * x (Equiv.swap i none none) = 1
      rw [Equiv.swap_apply_right, ← hu, Units.inv_mul]
    | some j => rfl
  have heval : eval₂ f (fun j => x (e j)) (MvPolynomial.rename e H) = eval₂ f x H := by
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext j
    exact congrArg x (Equiv.swap_apply_self i none j)
  have hr := homogeneous_eval₂_mul f (MvPolynomial.rename e H) m
    hH.rename_isHomogeneous ((u⁻¹ : Aˣ) : A) (fun j => x (e j))
  rw [hnorm, heval] at hr
  exact (eval₂_dehomogenize f _ _).trans hr

end Plane

end Cylinder.HomogeneousTorusRescaling

end
