module

public import Cylinder.ProductFrobeniusRelation
public import Cylinder.ProductFractions
public import Cylinder.ProductEvaluationRelation
public import Cylinder.ProductRescaling
public import Cylinder.ProductRescaledFractions

/-! Product residues, the rational identity, and the full-support evaluation
relation use one and the same actual nonzero coefficient family. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProductProposition

open MvPolynomial Finset
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductResidueTransport
open Cylinder.ProductExpansion Cylinder.ProductFrobeniusRelation
open Cylinder.ProductFractions Cylinder.ProductEvaluationRelation

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [CharP K p]

/-- All conclusions of the product proposition for the canonical plane equations,
including the relation over the field used for the algebraic arguments. -/
theorem product_and_full_support_relation {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : DualPoint p → ZMod p,
      (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      blackProduct p S = ∑ E ∈ whitePoints p S, C (c E) * whiteProductExcept p S E ∧
      fractionMap p (blackProduct p S) / fractionMap p (whiteProduct p S) =
        ∑ E ∈ whitePoints p S, fractionMap p (C (c E)) / fractionMap p (planeForm p E) ∧
      (∑ E ∈ whitePoints p S, C (c E) * planeForm p E ^ (p - 2)) = 0 ∧
      (∀ E : whitePoints p S, primeEmbedding p (K := K) (c E.val) ≠ 0) ∧
      PowerEvaluationRelation.Relation
        (fun E : whitePoints p S => fun j =>
          primeEmbedding p (K := K) (coefficientVector p E.val j))
        (fun E => primeEmbedding p (K := K) (c E.val)) (p - 2) := by
  obtain ⟨c, hc, hprod, hpower⟩ := exists_nonzero_product_and_frobenius_coefficients p hcard hS
  have hpower' : (∑ E : whitePoints p S,
      C (c E.val) * planeForm p E.val ^ (p - 2)) = 0 := by
    calc
      _ = ∑ E ∈ whitePoints p S, C (c E) * planeForm p E ^ (p - 2) :=
        Finset.sum_coe_sort _ _
      _ = 0 := hpower
  have hrelation := full_support_relation_over_field p (K := K) S (fun E => c E.val)
    (fun E => hc E.val E.property) hpower'
  exact ⟨c, hc, hprod, fraction_identity_of_product p S c hprod, hpower, hrelation⟩

theorem scaled_plane_as_linearForm (a : DualPoint p → ZMod p) (H : DualPoint p) :
    PowerEvaluationRelation.linearForm (fun j => a H * coefficientVector p H j) =
      ProductRescaling.scaledPlaneForm p a H := by
  simp only [PowerEvaluationRelation.linearForm, coefficientVector,
    ProductRescaling.scaledPlaneForm, planeForm, linearForm, map_mul, mul_sum, mul_assoc]

/-- The full proposition allows every nonzero rational rescaling of the plane
equations. The representative lemma in ProductRescaling proves that these are
all nonzero rational linear equations of the actual planes. -/
theorem scaled_product_and_full_support_relation {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (a : DualPoint p → ZMod p)
    (hwhite : ∀ H ∈ whitePoints p S, a H ≠ 0)
    (hblack : ∀ H ∈ blackPoints p S, a H ≠ 0) :
    ∃ c : DualPoint p → ZMod p,
      (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      (∏ H ∈ blackPoints p S, ProductRescaling.scaledPlaneForm p a H ^ weight p S H) =
        ∑ E ∈ whitePoints p S, C (c E) *
          (∏ H ∈ (whitePoints p S).erase E, ProductRescaling.scaledPlaneForm p a H) ∧
      fractionMap p (∏ H ∈ blackPoints p S, ProductRescaling.scaledPlaneForm p a H ^ weight p S H) /
          fractionMap p (∏ H ∈ whitePoints p S, ProductRescaling.scaledPlaneForm p a H) =
        ∑ E ∈ whitePoints p S,
          fractionMap p (C (c E)) / fractionMap p (ProductRescaling.scaledPlaneForm p a E) ∧
      (∑ E ∈ whitePoints p S, C (c E) * ProductRescaling.scaledPlaneForm p a E ^ (p - 2)) = 0 ∧
      (∀ E : whitePoints p S, primeEmbedding p (K := K) (c E.val) ≠ 0) ∧
      PowerEvaluationRelation.Relation
        (fun E : whitePoints p S => fun j =>
          primeEmbedding p (K := K) (a E.val * coefficientVector p E.val j))
        (fun E => primeEmbedding p (K := K) (c E.val)) (p - 2) := by
  obtain ⟨c, hc, hprod, hpower⟩ :=
    ProductRescaling.exists_rescaled_product_and_frobenius_coefficients p hcard hS a hwhite hblack
  have hzero : PowerEvaluationRelation.powerSum
      (fun E : whitePoints p S => fun j => a E.val * coefficientVector p E.val j)
      (fun E => c E.val) (p - 2) = 0 := by
    unfold PowerEvaluationRelation.powerSum
    simp only [scaled_plane_as_linearForm]
    calc
      _ = ∑ E ∈ whitePoints p S, C (c E) * ProductRescaling.scaledPlaneForm p a E ^ (p - 2) :=
        Finset.sum_coe_sort _ _
      _ = 0 := hpower
  have hrel := PowerRelationScalarExtension.relation_of_mapped_power_identity p
    (primeEmbedding p (K := K))
    (fun E : whitePoints p S => fun j => a E.val * coefficientVector p E.val j)
    (fun E => c E.val) (p - 2) (by have hp := (Fact.out : p.Prime).two_le; omega) hzero
  exact ⟨c, hc, hprod,
    ProductRescaledFractions.scaled_fraction_identity_of_product p S a hwhite c hprod,
    hpower, PowerRelationScalarExtension.coefficients_nonzero (primeEmbedding p) _
      (fun E : whitePoints p S => hc E.val E.property), hrel⟩

end Cylinder.ProductProposition

end
