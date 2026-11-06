module

public import Cylinder.PlaneCurveFactors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Adding the actual component bounds without assuming a global point bound. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.CurvePointAggregation

open MvPolynomial Cylinder.PlaneCurveFactors Cylinder.RationalPlaneLine

theorem sum_polar_bounds {I : Type*} (T : Finset I) (e N : I → ℕ) (s p : ℕ)
    (hp : 1 ≤ p) (hdegree : (∑ i ∈ T, e i) ≤ s)
    (hN : ∀ i ∈ T, 2 * N i ≤ e i * (e i + p - 1)) :
    2 * (∑ i ∈ T, N i) ≤ s * (s + p - 1) := by
  have hsum := Finset.sum_le_sum hN
  have heq : (∑ i ∈ T, e i * (e i + p - 1)) =
      (∑ i ∈ T, e i ^ 2) + (p - 1) * (∑ i ∈ T, e i) := by
    have hsub (i : I) : e i + p - 1 = e i + (p - 1) := by omega
    simp only [hsub, mul_add, Finset.sum_add_distrib, ← sq]
    rw [← Finset.sum_mul, mul_comm (∑ i ∈ T, e i) (p - 1)]
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := T) (f := e) (fun i _ => Nat.zero_le (e i))
  have hmul : (p - 1) * (∑ i ∈ T, e i) ≤ (p - 1) * s := Nat.mul_le_mul_left _ hdegree
  have hs : (∑ i ∈ T, e i) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hdegree 2
  have hright : s + p - 1 = s + (p - 1) := by omega
  rw [heq, ← Finset.mul_sum] at hsum
  rw [hright]
  nlinarith

variable {K L : Type*} [Field K] [Field L]

/-- The distinct actual polynomial factors cover the zero set. Their degree
sum and their individual bounds imply the bound for the whole curve. -/
theorem curve_bound_of_factor_bounds (f : K →+* L) (D : Finset (PlanePoint K))
    (F : MvPolynomial (Fin 3) L) (hF0 : F ≠ 0) (s p : ℕ)
    (hp : 1 ≤ p) (hs : F.totalDegree ≤ s)
    (hbound : ∀ G ∈ factors F, 2 * (zeroSet f D G).card ≤ G.totalDegree * (G.totalDegree + p - 1)) :
    2 * (zeroSet f D F).card ≤ s * (s + p - 1) := by
  have hcard : (zeroSet f D F).card ≤ ∑ G ∈ factors F, (zeroSet f D G).card := by
    rw [rational_zeroSet_eq_union f D F hF0]
    exact Finset.card_biUnion_le
  exact (Nat.mul_le_mul_left 2 hcard).trans
    (sum_polar_bounds (factors F) (fun G => G.totalDegree) (fun G => (zeroSet f D G).card)
      s p hp ((factors_degree_sum_le F hF0).trans hs) hbound)

end Cylinder.CurvePointAggregation

end
