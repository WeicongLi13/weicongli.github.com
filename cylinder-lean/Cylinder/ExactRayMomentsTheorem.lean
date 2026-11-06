module

public import Cylinder.ExactRayMomentsResidueRelation

/-! The full first-nonzero-moment proposition, for the actual normalized
product residues and the actual canonical projection rays, over every
field of characteristic p. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsTheorem
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection Cylinder.BlackProjectionVandermonde
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsActualProduct
open Cylinder.ExactRayMomentsActual Cylinder.ExactRayMomentsRaySums
open Cylinder.ExactRayMomentsCanonicalTimes
open Cylinder.ExactRayMomentsResidueRelation Cylinder.EvaluationProjection
open Cylinder.ProductFrobenius Cylinder.ProductRescaling Cylinder.ProductEvaluationRelation
variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [CharP K p]

def rayResiduesOverField {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : BlackProjection.directionSet p S b hb) (ν : Fin (BlackProjection.raySize p S b hb i)) : K :=
  primeEmbedding p (rayResidues p hb c i ν)

theorem rayMoment_map {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : BlackProjection.directionSet p S b hb) (j : ℕ) :
    rayMoment (BlackProjection.raySize p S b hb) (rayTimesOverField p (K := K) hb)
      (rayResiduesOverField p hb c) i j =
      primeEmbedding p (rayMoment (BlackProjection.raySize p S b hb)
        (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb)) (rayResidues p hb c) i j) := by
  simp only [rayMoment, rayTimesOverField, rayResiduesOverField, map_sum, map_mul, map_pow]

theorem same_residue_ray_relation_over_field {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) :
    EvaluationRelation (directionRepresentatives p (K := K) hb) (BlackProjection.raySize p S b hb)
      (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2) := by
  let I := BlackProjection.directionSet p S b hb
  let r := BlackProjection.raySize p S b hb
  let t := rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb)
  let v : (Σ i : I, Fin (r i)) → Option (Fin 3) → ZMod p :=
    fun x => rayPoint x.1.val.rep (t x.1 x.2)
  have hbase : Cylinder.PowerEvaluationRelation.Relation v
      (fun x => rayResidues p hb c x.1 x.2) (p - 2) := by
    intro F hF
    rw [Fintype.sum_sigma]
    exact same_residue_ray_relation p hb c hpower F hF
  have hmapped := Cylinder.PowerRelationScalarExtension.relation_scalar_extension p
    (primeEmbedding p (K := K)) v (fun x => rayResidues p hb c x.1 x.2) (p - 2)
    (by have hp := (Fact.out : p.Prime).two_le; omega) hbase
  have hv : (fun x j => primeEmbedding p (K := K) (v x j)) =
      fun x : (Σ i : I, Fin (r i)) => rayPoint (directionRepresentatives p hb x.1)
        (rayTimesOverField p hb x.1 x.2) := by
    funext x j
    cases j <;> rfl
  rw [hv] at hmapped
  intro F hF
  have h := hmapped F hF
  rw [Fintype.sum_sigma] at h
  exact h

/-- Proposition `prop:exactmoments`, with the same actual product residues
in every displayed conclusion. The sole extra bound is the original w ≤ p-2. -/
theorem exists_product_exact_moments {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (hw : weight p S b ≤ p - 2) :
    ∃ c : DualPoint p → ZMod p,
      (∀ H ∈ whitePoints p S, c H ≠ 0) ∧
      ((∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
        ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
          ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H) ∧
      ((∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) ∧
      (∀ i ν, rayResiduesOverField p (K := K) hb c i ν ≠ 0) ∧
      EvaluationRelation (directionRepresentatives p (K := K) hb) (BlackProjection.raySize p S b hb)
        (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2) ∧
      (∀ j, j < weight p S b → ∀ i, rayMoment (BlackProjection.raySize p S b hb)
        (rayTimesOverField p hb) (rayResiduesOverField p (K := K) hb c) i j = 0) ∧
      (∀ i, rayMoment (BlackProjection.raySize p S b hb) (rayTimesOverField p hb)
        (rayResiduesOverField p (K := K) hb c) i (weight p S b) ≠ 0) ∧
      Cylinder.PowerEvaluationRelation.Relation (directionRepresentatives p (K := K) hb)
        (fun i => rayMoment (BlackProjection.raySize p S b hb) (rayTimesOverField p hb)
          (rayResiduesOverField p hb c) i (weight p S b)) (p - 2 - weight p S b) := by
  obtain ⟨c, hc, hprod, hpower, hlow, hfirst⟩ := exists_actual_exact_moments p hcard hS hb
  have hrel := same_residue_ray_relation_over_field p (K := K) hb c hpower
  refine ⟨c, hc, hprod, hpower, ?_, hrel, ?_, ?_, ?_⟩
  · intro i ν hz
    apply hc (rayWhitePoint p hb i ν).val (rayWhitePoint p hb i ν).property
    exact (primeEmbedding p (K := K)).injective (by simpa only [rayResiduesOverField,
      rayResidues, map_zero] using hz)
  · intro j hj i
    have hFp : rayMoment (BlackProjection.raySize p S b hb)
        (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb)) (rayResidues p hb c) i j = 0 :=
      (moment_eq_ray_sum p hb c i j).symm.trans (hlow j hj i.val)
    rw [rayMoment_map, hFp, map_zero]
  · intro i
    have hFp : rayMoment (BlackProjection.raySize p S b hb)
        (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb)) (rayResidues p hb c) i (weight p S b) ≠ 0 := by
      have h := hfirst i
      rw [moment_eq_ray_sum p hb c i (weight p S b)] at h
      exact h
    rw [rayMoment_map]
    intro hz
    exact hFp ((primeEmbedding p (K := K)).injective (by simpa only [map_zero] using hz))
  · exact Cylinder.RayMomentRelations.relation_of_moments _ _ _ _ _ _ hw hrel

theorem weight_one_full_support_direction_relation {S : Finset (Geometry.Point p)}
    (hp : 3 ≤ p) (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (hw : weight p S b = 1) :
    ∃ u : BlackProjection.directionSet p S b hb → K,
      (∀ i, u i ≠ 0) ∧ Cylinder.PowerEvaluationRelation.Relation
        (directionRepresentatives p (K := K) hb) u (p - 3) := by
  obtain ⟨c, _hc, _hprod, _hpower, _hcray, _hrel, _hlow, hfirst, hdirrel⟩ :=
    exists_product_exact_moments p (K := K) hcard hS hb (by omega)
  refine ⟨fun i => rayMoment (BlackProjection.raySize p S b hb) (rayTimesOverField p hb)
    (rayResiduesOverField p hb c) i 1, ?_, ?_⟩
  · simpa only [hw] using hfirst
  · simpa only [hw, Nat.sub_sub, Nat.reduceAdd] using hdirrel

end Cylinder.ExactRayMomentsTheorem
end
