module

public import Cylinder.ProductExpansion
public import Cylinder.ProductPsi

/-!
# The degree-`p-2` Frobenius relation of the actual product coefficients

The quotient derivative is cleared of denominators in the polynomial
ring. Its numerator is minus the square of the white product times the
required power relation. The actual zero numerator and nonzero product
then prove the relation.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductFrobeniusRelation

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductResidueTransport Cylinder.ProductExpansion
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

theorem whiteProduct_factor (S : Finset (Geometry.Point p))
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    planeForm p E * whiteProductExcept p S E = whiteProduct p S :=
  Finset.mul_prod_erase _ _ hE

theorem theta_constant (a : ZMod p) : theta p (C a) = 0 := by
  simp [theta]

theorem theta_whiteProductExcept_cross (S : Finset (Geometry.Point p))
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    whiteProduct p S * theta p (whiteProductExcept p S E) -
      whiteProductExcept p S E * theta p (whiteProduct p S) =
        -(whiteProduct p S) ^ 2 * planeForm p E ^ (p - 2) := by
  have hpow : planeForm p E ^ p = planeForm p E ^ 2 * planeForm p E ^ (p - 2) := by
    rw [← pow_add]
    congr 1
    have hp := (Fact.out : p.Prime).two_le
    omega
  rw [← whiteProduct_factor p S E hE, Derivation.leibniz, theta_planeForm, hpow]
  simp only [smul_eq_mul]
  ring

def coefficientPowerSum (S : Finset (Geometry.Point p)) (c : DualPoint p → ZMod p) : Form p :=
  ∑ E ∈ whitePoints p S, C (c E) * planeForm p E ^ (p - 2)

theorem theta_cross_residueSum (S : Finset (Geometry.Point p)) (c : DualPoint p → ZMod p) :
    whiteProduct p S * theta p (residueSum p S c) -
      residueSum p S c * theta p (whiteProduct p S) =
        -(whiteProduct p S) ^ 2 * coefficientPowerSum p S c := by
  have htheta (E : DualPoint p) :
      theta p (C (c E) * whiteProductExcept p S E) =
        C (c E) * theta p (whiteProductExcept p S E) := by
    rw [Derivation.leibniz, theta_constant]
    simp only [smul_eq_mul, mul_zero, add_zero]
  unfold residueSum coefficientPowerSum
  rw [map_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [htheta]
  calc
    _ = C (c E) * (whiteProduct p S * theta p (whiteProductExcept p S E) -
        whiteProductExcept p S E * theta p (whiteProduct p S)) := by ring
    _ = _ := by rw [theta_whiteProductExcept_cross p S E hE]; ring

theorem coefficientPowerSum_eq_zero_of_product {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (c : DualPoint p → ZMod p)
    (hprod : blackProduct p S = residueSum p S c) : coefficientPowerSum p S c = 0 := by
  have hcross := ProductPsi.theta_cross_product_zero p hcard hS
  rw [hprod, theta_cross_residueSum] at hcross
  have hn : -(whiteProduct p S) ^ 2 ≠ 0 := neg_ne_zero.mpr
    (pow_ne_zero _ (whiteProduct_ne_zero p S))
  exact (mul_eq_zero.mp hcross).resolve_left hn

/-- The actual product residues satisfy the manuscript's degree-`p-2` power identity. -/
theorem exists_nonzero_product_and_frobenius_coefficients {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : DualPoint p → ZMod p, (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      blackProduct p S = ∑ E ∈ whitePoints p S, C (c E) * whiteProductExcept p S E ∧
      (∑ E ∈ whitePoints p S, C (c E) * planeForm p E ^ (p - 2)) = 0 := by
  obtain ⟨c, hc, hprod⟩ := exists_nonzero_product_coefficients p hcard hS
  exact ⟨c, hc, hprod, coefficientPowerSum_eq_zero_of_product p hcard hS c hprod⟩

#print axioms theta_whiteProductExcept_cross
#print axioms exists_nonzero_product_and_frobenius_coefficients

end Cylinder.ProductFrobeniusRelation

end
