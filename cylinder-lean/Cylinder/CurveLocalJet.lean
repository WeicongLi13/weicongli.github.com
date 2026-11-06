module

public import Cylinder.CurveLocalParameter

/-!
# Contact of two actual polynomial equations on the smooth parameter

If their values vanish and their gradients are proportional at the
origin, restriction of the second equation to the constructed smooth
parameter has order at least two. This is a power series statement,
without identifying it with a local intersection length.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurveLocalJet

open MvPolynomial Cylinder.CurveLocalParameter
open scoped Classical

variable {K : Type*} [Field K]

theorem vector_zero : (![0, 0] : Fin 2 → K) = 0 := by
  ext i
  fin_cases i <;> rfl

theorem X_sq_dvd_of_value_firstCoefficient_zero (f : PowerSeries K)
    (hzero : f.constantCoeff = 0) (hfirst : PowerSeries.coeff 1 f = 0) :
    (PowerSeries.X : PowerSeries K) ^ 2 ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
  · exact hfirst

theorem parameter_tangent_equation (F : PlanePolynomial (K := K)) (y : PowerSeries K)
    (hy0 : y.constantCoeff = 0) (hyF : along PowerSeries.X y F = 0) :
    eval (0 : Fin 2 → K) (pderiv 0 F) +
      eval (0 : Fin 2 → K) (pderiv 1 F) * PowerSeries.coeff 1 y = 0 := by
  have h := firstCoefficient_along F PowerSeries.X y
  rw [hyF, map_zero] at h
  simpa only [PowerSeries.constantCoeff_X, hy0, vector_zero,
    PowerSeries.coeff_one_X, mul_one] using h.symm

theorem contact_order_ge_two_of_gradient_relation
    (F G : PlanePolynomial (K := K)) (y : PowerSeries K)
    (hy0 : y.constantCoeff = 0) (hyF : along PowerSeries.X y F = 0)
    (hG0 : eval (0 : Fin 2 → K) G = 0) (c : K)
    (hgradient : ∀ i : Fin 2, eval (0 : Fin 2 → K) (pderiv i G) =
      c * eval (0 : Fin 2 → K) (pderiv i F)) :
    (2 : ℕ∞) ≤ PowerSeries.order (along PowerSeries.X y G) := by
  have hconstant : (along PowerSeries.X y G).constantCoeff = 0 := by
    rw [constantCoeff_along]
    simpa only [PowerSeries.constantCoeff_X, hy0, vector_zero] using hG0
  have hfirst : PowerSeries.coeff 1 (along PowerSeries.X y G) = 0 := by
    rw [firstCoefficient_along]
    simp only [PowerSeries.constantCoeff_X, hy0, vector_zero,
      PowerSeries.coeff_one_X, mul_one, hgradient]
    have ht := parameter_tangent_equation F y hy0 hyF
    calc
      _ = c * (eval (0 : Fin 2 → K) (pderiv 0 F) +
        eval (0 : Fin 2 → K) (pderiv 1 F) * PowerSeries.coeff 1 y) := by ring
      _ = 0 := by rw [ht, mul_zero]
  apply PowerSeries.nat_le_order_iff.mpr
  exact PowerSeries.X_pow_dvd_iff.mp
    (X_sq_dvd_of_value_firstCoefficient_zero _ hconstant hfirst)

theorem exists_parameter_contact_order_ge_two
    (F G : PlanePolynomial (K := K))
    (hF0 : eval (0 : Fin 2 → K) F = 0)
    (hFy : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0)
    (hG0 : eval (0 : Fin 2 → K) G = 0) (c : K)
    (hgradient : ∀ i : Fin 2, eval (0 : Fin 2 → K) (pderiv i G) =
      c * eval (0 : Fin 2 → K) (pderiv i F)) :
    ∃ y : PowerSeries K, y.constantCoeff = 0 ∧ along PowerSeries.X y F = 0 ∧
      (2 : ℕ∞) ≤ PowerSeries.order (along PowerSeries.X y G) := by
  obtain ⟨y, hy0, hyF⟩ := exists_parameter F hF0 hFy
  exact ⟨y, hy0, hyF, contact_order_ge_two_of_gradient_relation F G y hy0 hyF hG0 c hgradient⟩

end Cylinder.CurveLocalJet

end
