module

public import Cylinder.CurvePolarLocal

/-!
# The actual smooth parameter of a self-polar equation

The self-polar polynomial divisibility is pulled into the affine chart.
Differentiation inside the actual power series ring proves `y''=0`,
and hence contact of order at least the characteristic with the tangent.
Exclusion of the self-polar curve still requires a degree/intersection
argument; no such exclusion is assumed or asserted here.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurveSelfPolarParameter

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open Cylinder.FrobeniusPolar
open scoped BigOperators Classical

variable {K : Type*} [Field K]

def affinePolar (p n : ℕ) (F : PlanePolynomial (K := K)) : PlanePolynomial (K := K) :=
  C (n : K) * F + (X 0 ^ p - X 0) * pderiv 0 F + (X 1 ^ p - X 1) * pderiv 1 F

theorem dehomogenize_polar (p n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) :
    dehomogenize (polar p Q) = affinePolar p n (dehomogenize Q) := by
  have h := congrArg dehomogenize (FrobeniusPolarDifferential.polar_sub_euler p n Q hQ)
  simp only [map_sub, map_add, map_mul, map_pow, dehomogenize_C,
    Fintype.sum_option, dehomogenize_X_none, dehomogenize_X_some,
    one_pow, sub_self, zero_mul, zero_add, ← pderiv_dehomogenize,
    Fin.sum_univ_two] at h
  unfold affinePolar
  linear_combination h

variable (p : ℕ) [CharP K p]

theorem powerSeries_derivative_pow_char (z : PowerSeries K) :
    PowerSeries.derivative (z ^ p) = 0 := by
  have hp : (p : PowerSeries K) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (PowerSeries.C : K →+* PowerSeries K) (CharP.cast_eq_zero K p)
  rw [Derivation.leibniz_pow]
  simp [nsmul_eq_mul, hp]

theorem second_derivative_of_self_polar (n : ℕ) (F : PlanePolynomial (K := K))
    (x y : PowerSeries K) (hx : PowerSeries.derivative x = 1)
    (hyF : along x y F = 0) (hfy : along x y (pderiv 1 F) ≠ 0)
    (hdiv : F ∣ affinePolar p n F) :
    PowerSeries.derivative (PowerSeries.derivative y) = 0 := by
  let fx := along x y (pderiv 0 F)
  let fy := along x y (pderiv 1 F)
  let A := x ^ p - x
  let B := y ^ p - y
  have hchain := derivative_along F x y
  rw [hyF, map_zero, hx, mul_one] at hchain
  have hc : fx + fy * PowerSeries.derivative y = 0 := hchain.symm
  have hpolar : A * fx + B * fy = 0 := by
    obtain ⟨G, hG⟩ := hdiv
    have hz : along x y (affinePolar p n F) = 0 := by
      rw [hG, map_mul, hyF, zero_mul]
    simp only [affinePolar, map_add, map_mul, map_sub, map_pow, hyF,
      mul_zero, zero_add] at hz
    simpa [A, B, fx, fy, along] using hz
  have hrel : A * PowerSeries.derivative y = B := by
    have hm : fy * (A * PowerSeries.derivative y - B) = 0 := by
      linear_combination A * hc - hpolar
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hfy)
  have hAderivative : PowerSeries.derivative A = -1 := by
    simp only [A, map_sub, powerSeries_derivative_pow_char, hx, zero_sub]
  have hAnonzero : A ≠ 0 := by
    intro hA
    rw [hA, map_zero] at hAderivative
    exact one_ne_zero (neg_eq_zero.mp hAderivative.symm)
  have h := congrArg PowerSeries.derivative hrel
  simp only [Derivation.leibniz, smul_eq_mul, hAderivative, B, map_sub,
    powerSeries_derivative_pow_char, zero_sub] at h
  have hm : A * PowerSeries.derivative (PowerSeries.derivative y) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hm).resolve_left hAnonzero

theorem exists_self_polar_parameter (n : ℕ) (F : PlanePolynomial (K := K))
    (hF0 : eval (0 : Fin 2 → K) F = 0)
    (hFy : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0)
    (hdiv : F ∣ affinePolar p n F) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧ along PowerSeries.X y F = 0 ∧
      (p : ℕ∞) ≤ PowerSeries.order (y - FrobeniusPolarSeries.linearTruncation y) := by
  obtain ⟨y, hy0, hyF⟩ := exists_parameter F hF0 hFy
  have hfy : along PowerSeries.X y (pderiv 1 F) ≠ 0 := by
    intro hzero
    have h := congrArg PowerSeries.constantCoeff hzero
    rw [constantCoeff_along, map_zero] at h
    simp only [PowerSeries.constantCoeff_X, hy0, CurveLocalJet.vector_zero] at h
    exact hFy h
  have hsecond := second_derivative_of_self_polar p n F PowerSeries.X y
    PowerSeries.derivative_X hyF hfy hdiv
  exact ⟨y, hy0, hyF, FrobeniusPolarSeries.order_sub_linearTruncation_ge_char p y hsecond⟩

theorem exists_homogeneous_self_polar_parameter (n : ℕ)
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n)
    (hzero : eval origin Q = 0) (hY : eval origin (pderiv (some 1) Q) ≠ 0)
    (hdiv : Q ∣ polar p Q) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧ along PowerSeries.X y (dehomogenize Q) = 0 ∧
      (p : ℕ∞) ≤ PowerSeries.order (y - FrobeniusPolarSeries.linearTruncation y) := by
  apply exists_self_polar_parameter p n (dehomogenize Q)
  · rwa [eval_origin_dehomogenize]
  · rwa [pderiv_dehomogenize, eval_origin_dehomogenize]
  · rw [← dehomogenize_polar p n Q hQ]
    exact map_dvd dehomogenize hdiv

end Cylinder.CurveSelfPolarParameter

end
