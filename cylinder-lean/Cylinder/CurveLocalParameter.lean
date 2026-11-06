module

public import Cylinder.PowerSeriesAdicComplete
public import Cylinder.AdicSimpleRoot
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# An actual formal parameter at a smooth affine plane point

The polynomial `F` is evaluated at `(X,y)`. Its nonzero `Y` derivative
at the origin proves the existence of `y` with zero constant term by
Newton iteration in the proved complete power series ring.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurveLocalParameter

open MvPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Field K]

abbrev PlanePolynomial := MvPolynomial (Fin 2) K

theorem zeroCoordinates : (![0, 0] : Fin 2 → K) = 0 := by
  ext i
  fin_cases i <;> rfl

def along (x y : PowerSeries K) : PlanePolynomial (K := K) →+* PowerSeries K :=
  MvPolynomial.eval₂Hom PowerSeries.C ![x, y]

def inY : PlanePolynomial (K := K) →+* Polynomial (PowerSeries K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp PowerSeries.C)
    ![Polynomial.C PowerSeries.X, Polynomial.X]

theorem eval_inY (F : PlanePolynomial (K := K)) (y : PowerSeries K) :
    (inY F).eval y = along PowerSeries.X y F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [inY, along]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, Polynomial.eval_mul, hF]
    congr 1
    fin_cases i <;> simp [inY, along]

theorem derivative_inY (F : PlanePolynomial (K := K)) :
    (inY F).derivative = inY (pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [inY]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, Polynomial.derivative_mul, pderiv_mul, map_add, hF]
    fin_cases i <;> simp [inY]

theorem constantCoeff_along (F : PlanePolynomial (K := K)) (x y : PowerSeries K) :
    PowerSeries.constantCoeff (along x y F) =
      eval ![x.constantCoeff, y.constantCoeff] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [along]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    congr 1
    fin_cases i <;> simp [along]

theorem exists_parameter (F : PlanePolynomial (K := K)) (hF : eval (0 : Fin 2 → K) F = 0)
    (hFy : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧ along PowerSeries.X y F = 0 := by
  let I := PowerSeriesAdicComplete.xIdeal K
  have hinit : (inY F).eval 0 ∈ I := by
    rw [PowerSeriesAdicComplete.mem_xIdeal_iff_constantCoeff_eq_zero, eval_inY,
      constantCoeff_along]
    simpa only [PowerSeries.constantCoeff_X, map_zero, zeroCoordinates] using hF
  have hderivative : IsUnit ((inY F).derivative.eval 0) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, derivative_inY, eval_inY, constantCoeff_along]
    apply isUnit_iff_ne_zero.mpr
    simpa only [PowerSeries.constantCoeff_X, map_zero, zeroCoordinates] using hFy
  have hquotient : IsUnit (Ideal.Quotient.mk I ((inY F).derivative.eval 0)) :=
    hderivative.map (Ideal.Quotient.mk I)
  obtain ⟨y, hy, hy0⟩ := AdicSimpleRoot.exists_root I (inY F) 0 hinit hquotient
  refine ⟨y, ?_, ?_⟩
  · apply (PowerSeriesAdicComplete.mem_xIdeal_iff_constantCoeff_eq_zero K y).mp
    simpa only [I, sub_zero] using hy0
  · exact (eval_inY F y) ▸ hy

theorem derivative_along (F : PlanePolynomial (K := K)) (x y : PowerSeries K) :
    PowerSeries.derivative (along x y F) =
      along x y (pderiv 0 F) * PowerSeries.derivative x +
      along x y (pderiv 1 F) * PowerSeries.derivative y := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [along]
  | add F G hF hG => simp only [map_add, hF, hG]; ring
  | mul_X F i hF =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hF]
    fin_cases i <;> simp [along] <;> ring

theorem constantCoeff_derivative (y : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.derivative y) = PowerSeries.coeff 1 y := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp

theorem firstCoefficient_along (F : PlanePolynomial (K := K)) (x y : PowerSeries K) :
    PowerSeries.coeff 1 (along x y F) =
      eval ![x.constantCoeff, y.constantCoeff] (pderiv 0 F) * PowerSeries.coeff 1 x +
      eval ![x.constantCoeff, y.constantCoeff] (pderiv 1 F) * PowerSeries.coeff 1 y := by
  have h := congrArg PowerSeries.constantCoeff (derivative_along F x y)
  simpa only [constantCoeff_derivative, map_add, map_mul, constantCoeff_along] using h

theorem tangent_coefficient (F : PlanePolynomial (K := K)) (y : PowerSeries K)
    (hy0 : y.constantCoeff = 0) (hyF : along PowerSeries.X y F = 0)
    (hFy : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0) :
    PowerSeries.coeff 1 y = -eval (0 : Fin 2 → K) (pderiv 0 F) /
      eval (0 : Fin 2 → K) (pderiv 1 F) := by
  have h := firstCoefficient_along F PowerSeries.X y
  rw [hyF, map_zero] at h
  simp only [hy0, PowerSeries.constantCoeff_X, PowerSeries.coeff_one_X, mul_one] at h
  have hzero : (![0, 0] : Fin 2 → K) = 0 := by ext i; fin_cases i <;> rfl
  rw [hzero] at h
  apply (eq_div_iff hFy).mpr
  linear_combination -h

theorem exists_parameter_with_tangent (F : PlanePolynomial (K := K))
    (hF : eval (0 : Fin 2 → K) F = 0)
    (hFy : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧ along PowerSeries.X y F = 0 ∧
      PowerSeries.coeff 1 y = -eval (0 : Fin 2 → K) (pderiv 0 F) /
        eval (0 : Fin 2 → K) (pderiv 1 F) := by
  obtain ⟨y, hy0, hyF⟩ := exists_parameter F hF hFy
  exact ⟨y, hy0, hyF, tangent_coefficient F y hy0 hyF hFy⟩

end Cylinder.CurveLocalParameter

end
