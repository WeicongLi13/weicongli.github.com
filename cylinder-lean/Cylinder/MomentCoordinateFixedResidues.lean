module

public import Cylinder.FinalGlobalMoments

/-! Fixed product residues, without replacing the prescribed family by a
new existential choice.  This is the canonical input to chart transport. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.MomentCoordinateFixedResidues
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsActualProduct
open Cylinder.ExactRayMomentsActualBalance Cylinder.ExactRayMomentsSupportedProduct
open Cylinder.ExactRayMomentsLow Cylinder.ExactRayMomentsProduct
open Cylinder.ExactRayMomentsDirections Cylinder.ExactRayMomentsRaySums
open Cylinder.ExactRayMomentsResidueRelation Cylinder.ExactRayMomentsTheorem
open Cylinder.ProductRescaling Cylinder.EvaluationProjection Cylinder.FinalGlobalMoments
open Cylinder.BlackProjectionVandermonde Cylinder.RationalPlanePointModel
open Cylinder.GlobalMomentResidues
open Cylinder.DirectionCurveBounds

variable (p : ℕ) [Fact p.Prime]
local instance directionFintype : Fintype (BlackProjection.Direction p) := Fintype.ofFinite _

/-- The actual product identity forces the moments of the given residues. -/
theorem fixed_product_moments {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hprod : (∏ H ∈ blackPoints p S,
      scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H) :
    (∀ j, j < weight p S b → ∀ i, primeMoment p hb c i j = 0) ∧
      ∀ i, primeMoment p hb c i (weight p S b) ≠ 0 := by
  let P := blackPolynomial (blackDirection p S b) (fun i => directionForm i.rep)
    (fun _ => (1 : ZMod p)) (fun H => normalizedTime p b H.val)
    (fun H => weight p S H.val) (weight p S b)
  have hprodP : P = actualNumerator (whiteDirection p hb) (fun i => directionForm i.rep)
      (fun H => c H.val) (fun H => normalizedTime p b H.val) := by
    calc
      P = productCoordinateMap p b
          (∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) :=
        (actual_black_product_in_coordinates p hb).symm
      _ = _ := congrArg (productCoordinateMap p b) hprod
      _ = _ := actual_white_residue_in_coordinates p hb c
  have hm := supported_balanced_product_exact_moments
    (whiteDirection p hb) (blackDirection p S b) (fun i => directionForm i.rep)
    (all_direction_forms_prime p) (all_direction_forms_not_dvd p)
    (fun H => c H.val) (fun H => normalizedTime p b H.val)
    (fun _ => (1 : ZMod p)) (fun H => normalizedTime p b H.val) (fun _ => one_ne_zero)
    (fun H => weight p S H.val) (weight p S b) P hprodP rfl
    (supported_actual_weight_balance p hcard hS hb)
  constructor
  · intro j hj i
    exact (moment_eq_ray_sum p hb c i j).symm.trans (hm.1 j hj i.val)
  · intro i
    have hpos : 0 < ExactRayMomentsMultiplicity.directionExponent
        (whiteDirection p hb) (fun _ => 1) i.val := by
      rw [white_exponent_eq_raySize p hb i]
      exact ProjectiveProjection.raySize_pos (ZMod p) (Fin 3) (whiteImage p S)
        (coordinatePoint p b) (black_outside_whiteImage p hb) i
    have h := hm.2 i.val hpos
    rw [moment_eq_ray_sum p hb c i (weight p S b)] at h
    exact h

/-- All hypotheses required by the existing global theorem are consequences
of the two identities for the same prescribed product residues. -/
theorem fixed_product_global_moments {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S,
      scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) :
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ P, primeMoment p hb c P 2 = MvPolynomial.eval P.val.rep fg.1 * primeMoment p hb c P 1) ∧
      (∀ P, primeMoment p hb c P 3 = MvPolynomial.eval P.val.rep fg.2 * primeMoment p hb c P 1) := by
  have hw := SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb
  have hm := fixed_product_moments p hcard hS hb c hprod
  apply global_moments_unique_prime p hp hcard hS hnon hb c
  · intro i ν hz
    apply hc (ExactRayMomentsCanonicalTimes.rayWhitePoint p hb i ν).val
      (ExactRayMomentsCanonicalTimes.rayWhitePoint p hb i ν).property
    exact (ProductEvaluationRelation.primeEmbedding p (K := CurveField p)).injective
      (by simpa only [rayResiduesOverField, rayResidues, map_zero] using hz)
  · exact same_residue_ray_relation_over_field p hb c hpower
  · intro i
    rw [actualMoment_eq_embedding, hm.1 0 (by omega) i, map_zero]
  · intro i hz
    apply hm.2 i
    rw [hw]
    rw [actualMoment_eq_embedding] at hz
    exact (embedding p).injective (by simpa only [map_zero] using hz)

end Cylinder.MomentCoordinateFixedResidues
end
