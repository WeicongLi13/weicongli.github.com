module

public import Cylinder.ProductFrobenius
public import Cylinder.ProductIntersection

/-!
# The actual logarithmic Frobenius multiplier vanishes

This degree-`p-1` identity follows directly from true point-plane
incidence counts and finite-grid uniqueness. It is the vanishing of
the manuscript's `Psi`, not yet the degree-`p-2` relation involving
the product-residue coefficients, whose construction is separate.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductPsi

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.ProjectiveCover Cylinder.ProductFrobenius Cylinder.ProductIntersection
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def defect (S : Finset (Geometry.Point p)) (H : DualPoint p) : ZMod p :=
  (quotient p S H : ZMod p) - 1

theorem psi_eq_sum_defect (S : Finset (Geometry.Point p)) :
    psi p S = ∑ H : DualPoint p, C (defect p S H) * planeForm p H ^ (p - 1) := by
  unfold psi blackLog whiteLog blackPoints whitePoints WhiteBlackWeights.black WhiteBlackWeights.white
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hzero : quotient p S H = 0
  · simp [hzero, weight, defect]
  by_cases hone : quotient p S H = 1
  · simp [hone, weight, defect]
  have htwo : 2 ≤ quotient p S H := by omega
  have hpos : 1 ≤ quotient p S H := by omega
  simp [htwo, hzero, weight, defect, Nat.cast_sub hpos]

theorem psi_homogeneous (S : Finset (Geometry.Point p)) :
    (psi p S).IsHomogeneous (p - 1) := by
  rw [psi_eq_sum_defect]
  apply IsHomogeneous.sum
  intro H _
  simpa only [one_mul] using
    ((planeForm_homogeneous p H).pow (p - 1)).C_mul (defect p S H)

theorem sum_defect {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) : (∑ H : DualPoint p, defect p S H) = -1 := by
  unfold defect
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ H : DualPoint p, (quotient p S H : ZMod p)) = 0 := by
    rw [← Nat.cast_sum, sum_quotient p hcard hS]
    simp
  have hone : (∑ _H : DualPoint p, (1 : ZMod p)) = 1 := by
    simp [card_dualPoint, nsmul_eq_mul]
  rw [hsum, hone]
  simp

theorem sum_defect_through {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (x : PG3 p) :
    (∑ H ∈ IncidenceDoubleCount.through (Incident p) x, defect p S H) = -1 := by
  unfold defect
  rw [Finset.sum_sub_distrib]
  have hsum :
      (∑ H ∈ IncidenceDoubleCount.through (Incident p) x, (quotient p S H : ZMod p)) = 0 := by
    rw [← Nat.cast_sum]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr (sum_quotient_through_dvd p hcard hS x)
  have hone : (∑ _H ∈ IncidenceDoubleCount.through (Incident p) x, (1 : ZMod p)) = 1 := by
    simp [point_plane_count, nsmul_eq_mul]
  rw [hsum, hone]
  simp

theorem eval_psi_zero {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (v : ProjectiveGeometry.Vector p) : eval v (psi p S) = 0 := by
  rw [psi_eq_sum_defect, map_sum]
  simp only [map_mul, map_pow, eval_C, eval_planeForm]
  by_cases hv : v = 0
  · subst v
    have hp : p - 1 ≠ 0 := by have h := (Fact.out : p.Prime).two_le; omega
    simp [hp]
  let x : PG3 p := Projectivization.mk (ZMod p) v hv
  have hpower (H : DualPoint p) :
      (H.rep v) ^ (p - 1) = if Incident p x H then 0 else 1 := by
    simpa only [x, incident_mk_rep_iff, ite_not] using ZMod.pow_card_sub_one (H.rep v)
  simp_rw [hpower]
  calc
    (∑ H : DualPoint p, defect p S H * (if Incident p x H then 0 else 1)) =
        (∑ H : DualPoint p, defect p S H) -
          (∑ H ∈ IncidenceDoubleCount.through (Incident p) x, defect p S H) := by
      rw [IncidenceDoubleCount.through, Finset.sum_filter, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro H _
      by_cases hi : Incident p x H <;> simp [hi]
    _ = 0 := by rw [sum_defect p hcard hS, sum_defect_through p hcard hS x]; simp

/-- The genuine degree-`p-1` multiplier of the product derivative is zero as a polynomial. -/
theorem psi_eq_zero {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) : psi p S = 0 := by
  apply FiniteGrid.eq_zero_of_degreeOf_lt_card
  · intro i
    have hdegree := (psi_homogeneous p S).totalDegree_le
    have hi := degreeOf_le_totalDegree (psi p S) i
    have hp := (Fact.out : p.Prime).two_le
    simp only [ZMod.card]
    omega
  · exact eval_psi_zero p hcard hS

theorem theta_cross_product_zero {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    whiteProduct p S * theta p (blackProduct p S) -
      blackProduct p S * theta p (whiteProduct p S) = 0 := by
  rw [theta_cross_product, psi_eq_zero p hcard hS, mul_zero]

#print axioms psi_eq_zero
#print axioms theta_cross_product_zero

end Cylinder.ProductPsi

end
