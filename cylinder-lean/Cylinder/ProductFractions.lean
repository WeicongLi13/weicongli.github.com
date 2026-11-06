module

public import Cylinder.ProductExpansion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Field

/-!
# The product identity in the actual rational function field
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductFractions

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductResidueTransport Cylinder.ProductExpansion
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

abbrev RationalFunction := FractionRing (Form p)

def fractionMap : Form p →+* RationalFunction p := algebraMap _ _

theorem fractionMap_injective : Function.Injective (fractionMap p) :=
  IsFractionRing.injective _ _

theorem fraction_planeForm_ne_zero (E : DualPoint p) :
    fractionMap p (planeForm p E) ≠ 0 :=
  fun hz => planeForm_ne_zero p E (fractionMap_injective p (by simpa using hz))

theorem fraction_whiteProduct_ne_zero (S : Finset (Geometry.Point p)) :
    fractionMap p (whiteProduct p S) ≠ 0 :=
  fun hz => whiteProduct_ne_zero p S (fractionMap_injective p (by simpa using hz))

theorem removed_product_fraction (S : Finset (Geometry.Point p))
    (E : DualPoint p) (hE : E ∈ whitePoints p S) (c : ZMod p) :
    fractionMap p (C c * whiteProductExcept p S E) / fractionMap p (whiteProduct p S) =
      fractionMap p (C c) / fractionMap p (planeForm p E) := by
  apply (div_eq_div_iff (fraction_whiteProduct_ne_zero p S)
    (fraction_planeForm_ne_zero p E)).mpr
  have hfactor : fractionMap p (planeForm p E) * fractionMap p (whiteProductExcept p S E) =
      fractionMap p (whiteProduct p S) := by
    rw [← map_mul]
    exact congrArg (fractionMap p) (Finset.mul_prod_erase _ _ hE)
  rw [map_mul, ← hfactor]
  ring

theorem fraction_identity_of_product (S : Finset (Geometry.Point p))
    (c : DualPoint p → ZMod p)
    (hprod : blackProduct p S = residueSum p S c) :
    fractionMap p (blackProduct p S) / fractionMap p (whiteProduct p S) =
      ∑ E ∈ whitePoints p S, fractionMap p (C (c E)) / fractionMap p (planeForm p E) := by
  rw [hprod, residueSum, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro E hE
  exact removed_product_fraction p S E hE (c E)

theorem exists_nonzero_fraction_coefficients {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : DualPoint p → ZMod p, (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      fractionMap p (blackProduct p S) / fractionMap p (whiteProduct p S) =
        ∑ E ∈ whitePoints p S, fractionMap p (C (c E)) / fractionMap p (planeForm p E) := by
  obtain ⟨c, hc, hprod⟩ := exists_nonzero_product_coefficients p hcard hS
  exact ⟨c, hc, fraction_identity_of_product p S c hprod⟩

#print axioms fraction_identity_of_product
#print axioms exists_nonzero_fraction_coefficients

end Cylinder.ProductFractions

end
