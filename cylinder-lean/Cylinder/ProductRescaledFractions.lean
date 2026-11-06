module

public import Cylinder.ProductRescaling
public import Cylinder.ProductFractions

/-! The rational-function identity for every nonzero choice of rational plane equations. -/

@[expose] public section

noncomputable section

namespace Cylinder.ProductRescaledFractions

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductFractions Cylinder.ProductRescaling
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

theorem scaledPlaneForm_ne_zero (a : DualPoint p → ZMod p) (E : DualPoint p)
    (ha : a E ≠ 0) : scaledPlaneForm p a E ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr ha) (planeForm_ne_zero p E)

theorem fraction_scaledPlaneForm_ne_zero (a : DualPoint p → ZMod p) (E : DualPoint p)
    (ha : a E ≠ 0) : fractionMap p (scaledPlaneForm p a E) ≠ 0 :=
  fun hz => scaledPlaneForm_ne_zero p a E ha (fractionMap_injective p (by simpa using hz))

theorem fraction_scaled_whiteProduct_ne_zero (S : Finset (Geometry.Point p))
    (a : DualPoint p → ZMod p) (ha : ∀ E ∈ whitePoints p S, a E ≠ 0) :
    fractionMap p (∏ E ∈ whitePoints p S, scaledPlaneForm p a E) ≠ 0 := by
  intro hz
  have hprod : (∏ E ∈ whitePoints p S, scaledPlaneForm p a E) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun E hE => scaledPlaneForm_ne_zero p a E (ha E hE))
  exact hprod (fractionMap_injective p (by simpa using hz))

theorem scaled_removed_product_fraction (S : Finset (Geometry.Point p))
    (a : DualPoint p → ZMod p) (ha : ∀ E ∈ whitePoints p S, a E ≠ 0)
    (E : DualPoint p) (hE : E ∈ whitePoints p S) (c : ZMod p) :
    fractionMap p (C c * ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) /
        fractionMap p (∏ H ∈ whitePoints p S, scaledPlaneForm p a H) =
      fractionMap p (C c) / fractionMap p (scaledPlaneForm p a E) := by
  apply (div_eq_div_iff (fraction_scaled_whiteProduct_ne_zero p S a ha)
    (fraction_scaledPlaneForm_ne_zero p a E (ha E hE))).mpr
  have hfactor : fractionMap p (scaledPlaneForm p a E) *
      fractionMap p (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) =
      fractionMap p (∏ H ∈ whitePoints p S, scaledPlaneForm p a H) := by
    rw [← map_mul]
    exact congrArg (fractionMap p) (Finset.mul_prod_erase _ _ hE)
  rw [map_mul, ← hfactor]
  ring

theorem scaled_fraction_identity_of_product (S : Finset (Geometry.Point p))
    (a : DualPoint p → ZMod p) (ha : ∀ E ∈ whitePoints p S, a E ≠ 0)
    (c : DualPoint p → ZMod p)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, C (c E) *
        (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)) :
    fractionMap p (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) /
        fractionMap p (∏ H ∈ whitePoints p S, scaledPlaneForm p a H) =
      ∑ E ∈ whitePoints p S, fractionMap p (C (c E)) / fractionMap p (scaledPlaneForm p a E) := by
  rw [hprod, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro E hE
  exact scaled_removed_product_fraction p S a ha E hE (c E)

#print axioms scaled_fraction_identity_of_product

end Cylinder.ProductRescaledFractions

end
