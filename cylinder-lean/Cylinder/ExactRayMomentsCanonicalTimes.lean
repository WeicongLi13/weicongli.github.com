module

public import Cylinder.ExactRayMomentsNormalization

/-! The normalized product coordinates use exactly the existing canonical
ray parameters, after the actual white-point/ray-fibre equivalence. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsCanonicalTimes
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection Cylinder.BlackProjectionVandermonde
open Cylinder.ExactRayMomentsCoordinates Cylinder.ExactRayMomentsNormalization
variable (p : ℕ) [Fact p.Prime]

def rayWhitePoint {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) : whitePoints p S :=
  (whiteCoordinateEquiv p S).symm
    (rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb) i ν).val

theorem rayWhitePoint_coordinate {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) :
    coordinatePoint p (rayWhitePoint p hb i ν).val =
      (rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i ν).val.val :=
  congrArg Subtype.val ((whiteCoordinateEquiv p S).apply_symm_apply _)

theorem normalized_vector_eq_canonical {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) :
    normalizationScale p b (rayWhitePoint p hb i ν).val •
      transformedCoordinates p b (rayWhitePoint p hb i ν).val =
      normalizedVector (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i
        (rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb) i ν) := by
  let x := rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) i ν
  let H := rayWhitePoint p hb i ν
  have hHb : H.val ≠ b := ProjectiveLineCap.white_ne_black p H.property hb
  have hcoord : coordinatePoint p H.val = x.val.val := rayWhitePoint_coordinate p hb i ν
  have hdir : actualDirection p b H.val hHb = i.val := by
    unfold actualDirection
    simpa only [projectionIndex, projection, hcoord] using congrArg Subtype.val x.property
  obtain ⟨q, hq⟩ := exists_coordinate_rep_unit p H.val
  have hfull : (q : ZMod p) • transformedCoordinates p b H.val =
      coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H.val).rep := by
    change (q : ZMod p) • coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b)
      (dualCoordinates p H.val.rep) = _
    rw [← map_smul, ← Units.smul_def, hq]
  have hspatial : normalizationScale p b H.val •
      (fun j => transformedCoordinates p b H.val (some j)) = i.val.rep := by
    rw [← hdir]
    unfold normalizationScale
    rw [dite_eq_right hHb]
    exact (Classical.choose_spec (exists_noncentral_normalization p b H.val hHb)).2
  let u := normalisingUnit (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) i x
  have hu : (u : ZMod p) • directionVector (ZMod p) (Fin 3) (coordinatePoint p b) x.val.val =
      i.val.rep := normalisingUnit_spec (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i x
  have hother : ((u : ZMod p) * q) • (fun j => transformedCoordinates p b H.val (some j)) =
      i.val.rep := by
    rw [mul_smul]
    have htail : (q : ZMod p) • (fun j => transformedCoordinates p b H.val (some j)) =
        directionVector (ZMod p) (Fin 3) (coordinatePoint p b) x.val.val := by
      funext j
      have hj := congrFun hfull (some j)
      simpa only [Pi.smul_apply, smul_eq_mul, directionVector, hcoord] using hj
    rw [htail]
    exact hu
  have hraw : (fun j => transformedCoordinates p b H.val (some j)) ≠ 0 := by
    intro h
    apply i.val.rep_nonzero
    rw [← hspatial, h, smul_zero]
  have hscale : normalizationScale p b H.val = (u : ZMod p) * q :=
    smul_left_injective (ZMod p) hraw (hspatial.trans hother.symm)
  change normalizationScale p b H.val • transformedCoordinates p b H.val =
    (u : ZMod p) • coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b) x.val.val.rep
  rw [hscale, mul_smul, hfull, hcoord]

theorem normalized_time_eq_rayTimes {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) :
    normalizedTime p b (rayWhitePoint p hb i ν).val =
      rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i ν := by
  exact congrFun (normalized_vector_eq_canonical p hb i ν) none

end Cylinder.ExactRayMomentsCanonicalTimes
end
