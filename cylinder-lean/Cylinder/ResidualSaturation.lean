module

public import Cylinder.SaturatedPlaneLine

/-! Regular actual chart coordinates imply saturation; actual residual
colon ideals inherit both saturation and chart-coordinate regularity. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualSaturation

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.SaturatedPlaneLine
open scoped Classical

variable {R : Type*} [CommRing R]

theorem regular_cancel (J : Ideal R) (a P : R) (hregular : J.colon {a} = J)
    (hprod : a * P ∈ J) : P ∈ J := by
  apply hregular.le
  apply Submodule.mem_colon_singleton.mpr
  change P * a ∈ J
  simpa only [mul_comm] using hprod

theorem regular_power_cancel (J : Ideal R) (a P : R) (hregular : J.colon {a} = J)
    (n : ℕ) (hprod : a ^ n * P ∈ J) : P ∈ J := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hprod
  | succ n ih =>
    apply ih
    apply regular_cancel J a (a ^ n * P) hregular
    simpa only [pow_succ, mul_assoc, mul_left_comm] using hprod

theorem residual_coordinate_regular (J D : Ideal R) (a : R) (hregular : J.colon {a} = J) :
    (J.colon (D : Set R)).colon {a} = J.colon (D : Set R) := by
  apply le_antisymm
  · intro P hP
    apply Submodule.mem_colon.mpr
    intro H hH
    change P * H ∈ J
    apply regular_cancel J a (P * H) hregular
    have hPa := Submodule.mem_colon_singleton.mp hP
    have hprod := Submodule.mem_colon.mp hPa H hH
    change (P * a) * H ∈ J at hprod
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hprod
  · exact Ideal.le_colon

variable {K : Type*} [Field K]

theorem saturated_of_regular_chart (J : Ideal (PlaneRing K)) (L : PlaneRing K)
    (hL : L ∈ irrelevant (K := K)) (hregular : J.colon {L} = J) : Saturated J := by
  intro P n hP
  exact regular_power_cancel J L P hregular n (hP (L ^ n) (Ideal.pow_mem_pow hL n))

theorem residual_saturated (J D : Ideal (PlaneRing K)) (hJ : Saturated J) :
    Saturated (J.colon (D : Set (PlaneRing K))) := by
  intro P n hP
  apply Submodule.mem_colon.mpr
  intro H hH
  change P * H ∈ J
  apply hJ (P * H) n
  intro Q hQ
  have hprod := Submodule.mem_colon.mp (hP Q hQ) H hH
  change (Q * P) * H ∈ J at hprod
  simpa only [mul_assoc] using hprod

#print axioms regular_power_cancel
#print axioms residual_coordinate_regular
#print axioms saturated_of_regular_chart
#print axioms residual_saturated

end Cylinder.ResidualSaturation

end
