module

public import Cylinder.ProductCoordinates

/-!
# Nonzero residues at every actual white point

The actual empty-plane chart transports both point sets and polynomial
products. Scalars introduced by the chosen projective representatives
are nonzero and are included in the transported residue.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductResidueTransport

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveBalance Cylinder.ProductFrobenius Cylinder.ProductRestriction
open Cylinder.ProductResidue Cylinder.ProductCoordinates Cylinder.ProjectiveChart
open scoped BigOperators Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

def whiteProductExcept (S : Finset (Geometry.Point p)) (E : DualPoint p) : Form p :=
  ∏ H ∈ (whitePoints p S).erase E, planeForm p H

theorem transformed_product (g : Vector p ≃ₗ[ZMod p] Vector p)
    (T : Finset (DualPoint p)) (m : DualPoint p → ℕ) :
    ∃ a : ZMod p, a ≠ 0 ∧ polynomialEquiv p g.symm (∏ H ∈ T, planeForm p H ^ m H) =
      C a * ∏ H ∈ T, planeForm p (mapDual p g H) ^ m H := by
  let a : DualPoint p → ZMod p := fun H => Classical.choose (transformed_planeForm p g H)
  have ha (H : DualPoint p) : a H ≠ 0 ∧
      polynomialEquiv p g.symm (planeForm p H) = C (a H) * planeForm p (mapDual p g H) :=
    Classical.choose_spec (transformed_planeForm p g H)
  refine ⟨∏ H ∈ T, a H ^ m H, Finset.prod_ne_zero_iff.mpr (fun H _ =>
    pow_ne_zero _ (ha H).1), ?_⟩
  rw [map_prod]
  have hf : ∀ H ∈ T,
      polynomialEquiv p g.symm (planeForm p H ^ m H) =
        C (a H ^ m H) * planeForm p (mapDual p g H) ^ m H := by
    intro H _
    rw [map_pow, (ha H).2, mul_pow, ← map_pow]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, ← map_prod]

theorem whitePoints_image (g : Vector p ≃ₗ[ZMod p] Vector p)
    (S S' : Finset (Geometry.Point p))
    (hq : ∀ H, quotient p S' (mapDual p g H) = quotient p S H) :
    whitePoints p S' = (whitePoints p S).image (mapDual p g) := by
  have hu : Finset.univ.image (mapDual p g) = (Finset.univ : Finset (DualPoint p)) :=
    Finset.image_univ_of_surjective (mapDual_surjective p g)
  unfold whitePoints WhiteBlackWeights.white
  conv_lhs => rw [← hu]
  rw [Finset.filter_image]
  simp only [hq]

theorem blackPoints_image (g : Vector p ≃ₗ[ZMod p] Vector p)
    (S S' : Finset (Geometry.Point p))
    (hq : ∀ H, quotient p S' (mapDual p g H) = quotient p S H) :
    blackPoints p S' = (blackPoints p S).image (mapDual p g) := by
  have hu : Finset.univ.image (mapDual p g) = (Finset.univ : Finset (DualPoint p)) :=
    Finset.image_univ_of_surjective (mapDual_surjective p g)
  unfold blackPoints WhiteBlackWeights.black
  conv_lhs => rw [← hu]
  rw [Finset.filter_image]
  simp only [hq]

theorem transformed_blackProduct (g : Vector p ≃ₗ[ZMod p] Vector p)
    (S S' : Finset (Geometry.Point p))
    (hq : ∀ H, quotient p S' (mapDual p g H) = quotient p S H) :
    ∃ a : ZMod p, a ≠ 0 ∧
      polynomialEquiv p g.symm (blackProduct p S) = C a * blackProduct p S' := by
  obtain ⟨a, ha, hprod⟩ := transformed_product p g (blackPoints p S) (weight p S)
  refine ⟨a, ha, ?_⟩
  have ht : (∏ H ∈ blackPoints p S, planeForm p (mapDual p g H) ^ weight p S H) =
      blackProduct p S' := by
    unfold blackProduct
    rw [blackPoints_image p g S S' hq, Finset.prod_image (mapDual_injective p g).injOn]
    simp only [weight, hq]
  exact hprod.trans (congrArg (fun F => C a * F) ht)

theorem transformed_whiteProductExcept (g : Vector p ≃ₗ[ZMod p] Vector p)
    (S S' : Finset (Geometry.Point p)) (E : DualPoint p)
    (hq : ∀ H, quotient p S' (mapDual p g H) = quotient p S H)
    (hE : mapDual p g E = infinity p) :
    ∃ a : ZMod p, a ≠ 0 ∧
      polynomialEquiv p g.symm (whiteProductExcept p S E) =
        C a * (∏ H ∈ whiteWithoutInfinity p S', planeForm p H) := by
  obtain ⟨a, ha, hprod⟩ := transformed_product p g ((whitePoints p S).erase E) (fun _ => 1)
  refine ⟨a, ha, ?_⟩
  have ht : (∏ H ∈ (whitePoints p S).erase E, planeForm p (mapDual p g H)) =
      ∏ H ∈ whiteWithoutInfinity p S', planeForm p H := by
    unfold whiteWithoutInfinity
    rw [whitePoints_image p g S S' hq, ← hE,
      ← Finset.image_erase (mapDual_injective p g),
      Finset.prod_image (mapDual_injective p g).injOn]
  simpa only [whiteProductExcept, pow_one, ht] using hprod

theorem C_mul_dvd_of_dvd {a : ZMod p} (ha : a ≠ 0) {F G : Form p}
    (h : F ∣ G) : C a * F ∣ G := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨C (a⁻¹) * Q, ?_⟩
  rw [hQ]
  rw [show C a * F * (C (a⁻¹) * Q) = (C a * C (a⁻¹)) * (F * Q) by ring,
    ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

/-- Every white plane has its actual nonzero product residue. -/
theorem exists_white_residue {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    ∃ c : ZMod p, c ≠ 0 ∧ planeForm p E ∣
      blackProduct p S - C c * whiteProductExcept p S E := by
  have hempty := Cylinder.DualLineBalance.empty_of_white p hS hE
  obtain ⟨g, havoid, hginf, hsize, hdiv, hcy, hcounts⟩ :=
    Cylinder.EmptyPlaneChart.empty_plane_as_infinity p S E hempty
  let S' := S.image (chartMap p g)
  have hcard' : S'.card = p ^ 2 := hsize.trans hcard
  have hS' : Geometry.PDivisible p S' := hdiv.mpr hS
  have hq : ∀ H, quotient p S' (mapDual p g H) = quotient p S H := by
    intro H
    unfold quotient
    rw [hcounts H]
  obtain ⟨c', hc', hres⟩ := exists_infinity_residue_dvd p hcard' hS'
  obtain ⟨aP, haP, hP⟩ := transformed_blackProduct p g S S' hq
  obtain ⟨aN, haN, hN⟩ := transformed_whiteProductExcept p g S S' E hq hginf
  obtain ⟨aE, haE, hL⟩ := transformed_planeForm p g E
  rw [hginf] at hL
  refine ⟨aP * c' / aN, div_ne_zero (mul_ne_zero haP hc') haN, ?_⟩
  apply (map_dvd_iff (polynomialEquiv p g.symm)).mp
  rw [hL]
  apply C_mul_dvd_of_dvd p haE
  rw [map_sub, map_mul, polynomialEquiv_C, hP, hN, ← mul_assoc, ← map_mul,
    div_mul_cancel₀ _ haN]
  convert dvd_mul_of_dvd_right hres (C aP) using 1 <;> simp only [map_mul] <;> ring

#print axioms transformed_product
#print axioms exists_white_residue

end Cylinder.ProductResidueTransport

end
