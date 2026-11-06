module

public import Cylinder.AffinePolynomialTranslation
public import Cylinder.CurveSmoothPointExistence

/-!
# The constructed smooth parameter at an arbitrary affine point

The point can lie over an arbitrary field extension. Its coordinates
are translated explicitly; the original self-polar equation is
evaluated at `(a₀+X,a₁+y)`, so no rationality assumption on the point
is used in the Frobenius differential argument.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CurveParameterAtPoint

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.AffinePolynomialTranslation
open scoped Classical

variable {K : Type*} [Field K]

omit [Field K] in
theorem vector_eta (a : Fin 2 → K) : ![a 0, a 1] = a := by
  ext i
  fin_cases i <;> rfl

theorem exists_parameter_at_point (F : PlanePolynomial (K := K)) (a : Fin 2 → K)
    (hzero : eval a F = 0) (hY : eval a (pderiv 1 F) ≠ 0) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧
      along (PowerSeries.C (a 0) + PowerSeries.X) (PowerSeries.C (a 1) + y) F = 0 := by
  have hF0 : eval (0 : Fin 2 → K) (translate a F) = 0 := by
    rwa [eval_translate, add_zero]
  have hFy : eval (0 : Fin 2 → K) (pderiv 1 (translate a F)) ≠ 0 := by
    rwa [pderiv_translate, eval_translate, add_zero]
  obtain ⟨y, hy0, hyF⟩ := exists_parameter (translate a F) hF0 hFy
  rw [along_translate] at hyF
  exact ⟨y, hy0, hyF⟩

theorem partial_nonzero_on_parameter (F : PlanePolynomial (K := K)) (a : Fin 2 → K)
    (y : PowerSeries K) (hy0 : y.constantCoeff = 0) (hY : eval a (pderiv 1 F) ≠ 0) :
    along (PowerSeries.C (a 0) + PowerSeries.X) (PowerSeries.C (a 1) + y) (pderiv 1 F) ≠ 0 := by
  intro hzero
  have h := congrArg PowerSeries.constantCoeff hzero
  rw [constantCoeff_along, map_zero] at h
  simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
    hy0, add_zero, vector_eta] at h
  exact hY h

theorem parameter_tangent_coefficient (F : PlanePolynomial (K := K)) (a : Fin 2 → K)
    (y : PowerSeries K) (hy0 : y.constantCoeff = 0)
    (hyF : along (PowerSeries.C (a 0) + PowerSeries.X) (PowerSeries.C (a 1) + y) F = 0)
    (hY : eval a (pderiv 1 F) ≠ 0) :
    PowerSeries.coeff 1 y = -eval a (pderiv 0 F) / eval a (pderiv 1 F) := by
  have hF0 : along PowerSeries.X y (translate a F) = 0 := by
    rwa [along_translate]
  have hFy : eval (0 : Fin 2 → K) (pderiv 1 (translate a F)) ≠ 0 := by
    rwa [pderiv_translate, eval_translate, add_zero]
  have h := tangent_coefficient (translate a F) y hy0 hF0 hFy
  simpa only [pderiv_translate, eval_translate, add_zero] using h

theorem exists_self_polar_parameter_at_point (p n : ℕ) [CharP K p]
    (F : PlanePolynomial (K := K)) (a : Fin 2 → K)
    (hzero : eval a F = 0) (hY : eval a (pderiv 1 F) ≠ 0)
    (hdiv : F ∣ CurveSelfPolarParameter.affinePolar p n F) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧
      along (PowerSeries.C (a 0) + PowerSeries.X) (PowerSeries.C (a 1) + y) F = 0 ∧
      (p : ℕ∞) ≤ PowerSeries.order (y - FrobeniusPolarSeries.linearTruncation y) := by
  obtain ⟨y, hy0, hyF⟩ := exists_parameter_at_point F a hzero hY
  have hfy := partial_nonzero_on_parameter F a y hy0 hY
  have hx : PowerSeries.derivative (PowerSeries.C (a 0) + PowerSeries.X) = 1 := by simp
  have hsecond := CurveSelfPolarParameter.second_derivative_of_self_polar p n F
    (PowerSeries.C (a 0) + PowerSeries.X) (PowerSeries.C (a 1) + y) hx hyF hfy hdiv
  have hysecond : PowerSeries.derivative (PowerSeries.derivative y) = 0 := by
    simpa using hsecond
  exact ⟨y, hy0, hyF, FrobeniusPolarSeries.order_sub_linearTruncation_ge_char p y hysecond⟩

end Cylinder.CurveParameterAtPoint

end
