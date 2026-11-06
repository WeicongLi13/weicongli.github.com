module

public import Cylinder.CurveLocalJet
public import Cylinder.FrobeniusPolarSeries

/-!
# Restriction of the Frobenius polar to an actual smooth parameter

The three-variable homogeneous polynomial is dehomogenized by setting
its first variable to one. The local parameter is constructed, and
the proved polar gradient identity gives a restriction of order at
least two. No local intersection length or Bezout estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurvePolarLocal

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.FrobeniusPolar
open scoped BigOperators Classical

variable {K : Type*} [Field K]

abbrev HomogeneousPlanePolynomial := MvPolynomial (Option (Fin 2)) K

def origin : Option (Fin 2) → K := fun i => i.elim 1 0

def dehomogenize : HomogeneousPlanePolynomial (K := K) →+* PlanePolynomial (K := K) :=
  MvPolynomial.eval₂Hom C (fun i => i.elim 1 X)

@[simp] theorem dehomogenize_C (a : K) : dehomogenize (C a) = C a := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_X_none : dehomogenize (X none : HomogeneousPlanePolynomial (K := K)) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_X_some (i : Fin 2) :
    dehomogenize (X (some i) : HomogeneousPlanePolynomial (K := K)) = X i := by
  simp [dehomogenize]

theorem pderiv_dehomogenize (Q : HomogeneousPlanePolynomial (K := K)) (j : Fin 2) :
    pderiv j (dehomogenize Q) = dehomogenize (pderiv (some j) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, pderiv_mul, map_add, hF]
    cases i with
    | none => simp
    | some i => simp [pderiv_X, Pi.single_apply]

theorem eval_dehomogenize (Q : HomogeneousPlanePolynomial (K := K)) (x : Fin 2 → K) :
    eval x (dehomogenize Q) = eval (fun i => i.elim 1 x) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    cases i <;> simp

theorem eval_origin_dehomogenize (Q : HomogeneousPlanePolynomial (K := K)) :
    eval (0 : Fin 2 → K) (dehomogenize Q) = eval origin Q :=
  eval_dehomogenize Q 0

theorem origin_frobeniusFixed (p : ℕ) (hp : p ≠ 0) : FrobeniusFixed p (origin (K := K)) := by
  intro i
  cases i <;> simp [origin, hp]

variable (p : ℕ) [CharP K p]

theorem dehomogenized_polar_gradient (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hp : p ≠ 0) (j : Fin 2) :
    eval (0 : Fin 2 → K) (pderiv j (dehomogenize (polar p Q))) =
      ((n - 1 : ℕ) : K) * eval (0 : Fin 2 → K) (pderiv j (dehomogenize Q)) := by
  rw [pderiv_dehomogenize, pderiv_dehomogenize, eval_origin_dehomogenize,
    eval_origin_dehomogenize]
  have h := congrFun (gradient_polar_at_fixed p n Q hQ origin (origin_frobeniusFixed p hp)) (some j)
  change eval origin (pderiv (some j) (polar p Q)) = (n - 1) • eval origin (pderiv (some j) Q) at h
  simpa only [nsmul_eq_mul] using h

theorem exists_parameter_polar_order_ge_two (n : ℕ)
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n) (hp : p ≠ 0)
    (hzero : eval origin Q = 0) (hY : eval origin (pderiv (some 1) Q) ≠ 0) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧
      along PowerSeries.X y (dehomogenize Q) = 0 ∧
      (2 : ℕ∞) ≤ PowerSeries.order (along PowerSeries.X y (dehomogenize (polar p Q))) := by
  apply CurveLocalJet.exists_parameter_contact_order_ge_two
    (dehomogenize Q) (dehomogenize (polar p Q))
  · rwa [eval_origin_dehomogenize]
  · rwa [pderiv_dehomogenize, eval_origin_dehomogenize]
  · rw [eval_origin_dehomogenize]
    exact polar_vanishes_at_rational_zero p n Q hQ origin (origin_frobeniusFixed p hp) hzero
  · exact dehomogenized_polar_gradient p n Q hQ hp

end Cylinder.CurvePolarLocal

end
