module

public import Cylinder.ExactRayMomentsActual
public import Cylinder.ExactRayMomentsRaySums
public import Cylinder.RayMomentRelations

/-! The very same normalized product residues also give the degree p-2
relation on the actual canonical ray parameters. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsResidueRelation
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection Cylinder.BlackProjectionVandermonde
open Cylinder.ExactRayMomentsCoordinates Cylinder.ExactRayMomentsNormalization
open Cylinder.ExactRayMomentsCanonicalTimes Cylinder.ExactRayMomentsRaySums
open Cylinder.ProductFrobenius Cylinder.ProductRescaling Cylinder.ProductEvaluationRelation
open Cylinder.PowerEvaluationRelation Cylinder.LinearEvaluationTransport
variable (p : ℕ) [Fact p.Prime]

def rayWhiteEquiv {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    (Σ i : BlackProjection.directionSet p S b hb, Fin (BlackProjection.raySize p S b hb i)) ≃
      whitePoints p S :=
  ((Equiv.sigmaCongrRight (fun i => rayEnumeration (ZMod p) (Fin 3)
    (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb) i)).trans
    (Equiv.sigmaFiberEquiv (projectionIndex (ZMod p) (Fin 3) (whiteImage p S)
      (coordinatePoint p b) (black_outside_whiteImage p hb)))).trans (whiteCoordinateEquiv p S).symm

theorem rayWhiteEquiv_value {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S)
    (x : Σ i : BlackProjection.directionSet p S b hb, Fin (BlackProjection.raySize p S b hb i)) :
    rayWhiteEquiv p hb x = rayWhitePoint p hb x.1 x.2 := rfl

def rayResidues {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : BlackProjection.directionSet p S b hb) (ν : Fin (BlackProjection.raySize p S b hb i)) : ZMod p :=
  c (rayWhitePoint p hb i ν).val

theorem same_residue_coordinate_relation {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (c : DualPoint p → ZMod p)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) :
    Relation (fun H : whitePoints p S => normalizationScale p b H.val • transformedCoordinates p b H.val)
      (fun H => c H.val) (p - 2) := by
  have hz : powerSum
      (fun H : whitePoints p S => fun j => normalizationScale p b H.val * coefficientVector p H.val j)
      (fun H => c H.val) (p - 2) = 0 := by
    unfold powerSum
    simp only [Cylinder.ProductProposition.scaled_plane_as_linearForm]
    exact (Finset.sum_coe_sort _ _).trans hpower
  have hbase := relation_of_powerSum_eq_zero p _ _ (p - 2)
    (by have hp := (Fact.out : p.Prime).two_le; omega) hz
  have hreindex := relation_after_reindex (finSuccEquiv 3) _ _ _ hbase
  have hcoord : Relation
      (fun H : whitePoints p S => normalizationScale p b H.val • dualCoordinates p H.val.rep)
      (fun H => c H.val) (p - 2) := by
    simpa only [Pi.smul_def, smul_eq_mul, dualCoordinates_coefficientVector] using hreindex
  have hlinear := relation_after_linearEquiv _ _ _
    (coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b)) hcoord
  simpa only [map_smul, transformedCoordinates] using hlinear

theorem normalized_vector_eq_ray_point {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) :
      normalizationScale p b (rayWhitePoint p hb i ν).val •
        transformedCoordinates p b (rayWhitePoint p hb i ν).val =
      Cylinder.EvaluationProjection.rayPoint i.val.rep
        (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb) i ν) :=
    (normalized_vector_eq_canonical p hb i ν).trans
      (normalizedVector_eq_rayPoint (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i
        (rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb) i ν))

theorem same_residue_ray_relation {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) :
    Cylinder.EvaluationProjection.EvaluationRelation
      (fun i : BlackProjection.directionSet p S b hb => i.val.rep) (BlackProjection.raySize p S b hb)
      (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb)) (rayResidues p hb c) (p - 2) := by
  let v := fun H : whitePoints p S =>
    normalizationScale p b H.val • transformedCoordinates p b H.val
  have hbase : Relation v (fun H => c H.val) (p - 2) := same_residue_coordinate_relation p c hpower
  have hrel : Relation (fun x => v (rayWhiteEquiv p hb x))
      (fun x => c (rayWhiteEquiv p hb x).val) (p - 2) := by
    intro F hF
    rw [(rayWhiteEquiv p hb).sum_comp (fun H : whitePoints p S => c H.val * MvPolynomial.eval (v H) F)]
    exact hbase F hF
  have hveq : (fun x => v (rayWhiteEquiv p hb x)) =
      fun x : (Σ i : BlackProjection.directionSet p S b hb, Fin (BlackProjection.raySize p S b hb i)) =>
        Cylinder.EvaluationProjection.rayPoint x.1.val.rep
          (rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
            (black_outside_whiteImage p hb) x.1 x.2) := by
    funext x
    exact normalized_vector_eq_ray_point p hb x.1 x.2
  rw [hveq] at hrel
  intro F hF
  have h := hrel F hF
  rw [Fintype.sum_sigma] at h
  exact h

end Cylinder.ExactRayMomentsResidueRelation
end
