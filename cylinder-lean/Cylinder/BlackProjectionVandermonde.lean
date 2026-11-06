module

public import Cylinder.BlackProjectionLineCap
public import Cylinder.ProjectiveVandermonde
public import Cylinder.ProjectiveFieldEmbedding
public import Cylinder.ProductProposition

/-!
# Vandermonde on the actual prime-field black-point projection

The product relation is reindexed and rescaled to the genuine white
coordinate set. Normalized prime-field ray coordinates and coefficients
are then embedded in the curve field. Scalar extension tests every
homogeneous form over that field, not only forms over the prime field.
-/

@[expose] public section
noncomputable section

namespace Cylinder.BlackProjectionVandermonde

open MvPolynomial Cylinder.BlackProjection Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductEvaluationRelation Cylinder.ProjectiveProjection
open scoped Classical LinearAlgebra.Projectivization BigOperators

section Reindex

variable {K σ τ I : Type*} [Field K] [Fintype σ] [Fintype τ] [Fintype I]

omit [Fintype σ] [Fintype τ] in
theorem relation_after_reindex (e : σ ≃ τ) (v : I → σ → K) (c : I → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    PowerEvaluationRelation.Relation (fun i j => v i (e.symm j)) c d := by
  intro F hF
  simpa only [eval_rename, Function.comp_def] using
    hrel (rename e.symm F) (hF.rename_isHomogeneous (f := e.symm))

end Reindex

variable (p : ℕ) [Fact p.Prime]

theorem dualCoordinates_coefficientVector (H : DualPoint p) :
    dualCoordinates p H.rep = fun j => coefficientVector p H ((finSuccEquiv 3).symm j) := rfl

theorem dualCoordinates_rep_ne_zero (H : DualPoint p) : dualCoordinates p H.rep ≠ 0 := by
  intro h
  exact H.rep_nonzero ((dualCoordinates p).injective (by simpa using h))

theorem coordinatePoint_mk (H : DualPoint p) :
    coordinatePoint p H = Projectivization.mk (ZMod p) (dualCoordinates p H.rep)
      (dualCoordinates_rep_ne_zero p H) := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  rw [coordinatePoint, Projectivization.map_mk]
  rfl

def whiteCoordinateEquiv (S : Finset (Geometry.Point p)) : whitePoints p S ≃ whiteImage p S :=
  Equiv.ofBijective (fun H => ⟨coordinatePoint p H.val,
    Finset.mem_image.mpr ⟨H.val, H.property, rfl⟩⟩) (by
      constructor
      · intro H Q h
        exact Subtype.ext (coordinatePoint_injective p (congrArg Subtype.val h))
      · intro y
        obtain ⟨H, hH, hHy⟩ := Finset.mem_image.mp y.property
        exact ⟨⟨H, hH⟩, Subtype.ext hHy⟩)

theorem whiteImage_full_support {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    ProjectiveVandermonde.HasFullSupportRelation (ZMod p) (Fin 3) (whiteImage p S) (p - 2) := by
  obtain ⟨c, hc, _hprod, hpower⟩ :=
    ProductFrobeniusRelation.exists_nonzero_product_and_frobenius_coefficients p hcard hS
  have hpower' : (∑ H : whitePoints p S,
      C (c H.val) * ProductFrobenius.planeForm p H.val ^ (p - 2)) = 0 := by
    calc
      _ = ∑ H ∈ whitePoints p S, C (c H) * ProductFrobenius.planeForm p H ^ (p - 2) :=
        Finset.sum_coe_sort _ _
      _ = 0 := hpower
  have hrel := (full_support_relation_of_frobenius_identity p S (fun H => c H.val)
    (fun H => hc H.val H.property) hpower').2
  have hreindex := relation_after_reindex (finSuccEquiv 3)
    (fun H : whitePoints p S => coefficientVector p H.val) (fun H => c H.val) (p - 2) hrel
  have hcoordinates : PowerEvaluationRelation.Relation
      (fun H : whitePoints p S => dualCoordinates p H.val.rep) (fun H => c H.val) (p - 2) := by
    simpa only [dualCoordinates_coefficientVector] using hreindex
  exact ProjectiveFieldEmbedding.full_support_of_indexed_representatives (whiteImage p S)
    (fun H : whitePoints p S => dualCoordinates p H.val.rep)
    (fun H => dualCoordinates_rep_ne_zero p H.val) (whiteCoordinateEquiv p S)
    (fun H => coordinatePoint_mk p H.val) (fun H => c H.val)
    (fun H => hc H.val H.property) (p - 2) hcoordinates

variable {K : Type*} [Field K] [CharP K p]

abbrev directionRepresentatives {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : BlackProjection.directionSet p S b hb → Fin 3 → K :=
  fun i j => primeEmbedding p (i.val.rep j)

abbrev rayTimesOverField {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : ∀ i : BlackProjection.directionSet p S b hb,
      Fin (BlackProjection.raySize p S b hb i) → K :=
  fun i ν => primeEmbedding p (rayTimes (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) i ν)

theorem directionRepresentatives_ne_zero {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : ∀ i, directionRepresentatives p (K := K) hb i ≠ 0 := by
  intro i h
  apply i.val.rep_nonzero
  funext j
  exact (primeEmbedding p (K := K)).injective (by
    simpa only [map_zero, Pi.zero_apply] using congrFun h j)

theorem rayTimesOverField_injective {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : ∀ i, Function.Injective (rayTimesOverField p (K := K) hb i) :=
  fun i => (primeEmbedding p (K := K)).injective.comp
    (rayTimes_injective (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb) i)

theorem exists_normalized_relation_over_field {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : ∀ i : BlackProjection.directionSet p S b hb, Fin (BlackProjection.raySize p S b hb i) → K,
      (∀ i ν, c i ν ≠ 0) ∧ EvaluationProjection.EvaluationRelation
        (directionRepresentatives p hb) (BlackProjection.raySize p S b hb)
        (rayTimesOverField p hb) c (p - 2) := by
  obtain ⟨c, hc, hrel⟩ := whiteImage_full_support p hcard hS
  let d := p - 2
  let I := BlackProjection.directionSet p S b hb
  let r := BlackProjection.raySize p S b hb
  let t := rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb)
  let a := ProjectiveVandermonde.normalizedCoefficients (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) c d
  have ha : ∀ i ν, a i ν ≠ 0 :=
    ProjectiveVandermonde.normalizedCoefficients_ne_zero (ZMod p) (Fin 3) (whiteImage p S)
      (coordinatePoint p b) (black_outside_whiteImage p hb) c hc d
  have hnorm := ProjectiveVandermonde.normalized_evaluation_relation (ZMod p) (Fin 3)
    (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb) c d hrel
  let v : (Σ i : I, Fin (r i)) → Option (Fin 3) → ZMod p :=
    fun x => EvaluationProjection.rayPoint x.1.val.rep (t x.1 x.2)
  have hbase : PowerEvaluationRelation.Relation v (fun x => a x.1 x.2) d := by
    intro F hF
    rw [Fintype.sum_sigma]
    exact hnorm F hF
  have hmapped := PowerRelationScalarExtension.relation_scalar_extension p (primeEmbedding p (K := K))
    v (fun x => a x.1 x.2) d (by have hp := (Fact.out : p.Prime).two_le; dsimp [d]; omega) hbase
  refine ⟨fun i ν => primeEmbedding p (a i ν), ?_, ?_⟩
  · intro i ν hzero
    exact ha i ν ((primeEmbedding p (K := K)).injective (by simpa only [map_zero] using hzero))
  · intro F hF
    have hv : (fun x j => primeEmbedding p (K := K) (v x j)) =
        fun x : (Σ i : I, Fin (r i)) =>
          EvaluationProjection.rayPoint (directionRepresentatives p hb x.1)
            (rayTimesOverField p hb x.1 x.2) := by
      funext x j
      cases j <;> rfl
    rw [hv] at hmapped
    have h := hmapped F hF
    rw [Fintype.sum_sigma] at h
    exact h

theorem ray_lower_bound_of_independent [Infinite K] {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (a : ℕ) (ha : a ≤ p - 2)
    (hind : EvaluationProjection.Independent (directionRepresentatives p (K := K) hb) a)
    (i : BlackProjection.directionSet p S b hb) :
    p - 2 - a + 2 ≤ BlackProjection.raySize p S b hb i := by
  obtain ⟨c, hc, hrel⟩ := exists_normalized_relation_over_field p (K := K) hcard hS hb
  exact EvaluationProjection.ray_size_lower_bound_of_evaluation_relation
    (directionRepresentatives p hb) (directionRepresentatives_ne_zero p hb)
    (BlackProjection.raySize p S b hb)
    (raySize_pos (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) (rayTimesOverField p hb) c
    (rayTimesOverField_injective p hb) hc (p - 2) a ha hind hrel i

theorem dependent_in_degree_of_ray [Infinite K] {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb) :
    ¬ EvaluationProjection.Independent (directionRepresentatives p (K := K) hb)
      (p - BlackProjection.raySize p S b hb i - 1) := by
  intro hind
  have htwo := two_le_raySize p hcard hS hb i
  have hhalf := raySize_le_half p hcard hS hnon hb i
  have hlower := ray_lower_bound_of_independent p hcard hS hb _ (by omega) hind i
  omega

end Cylinder.BlackProjectionVandermonde

end
