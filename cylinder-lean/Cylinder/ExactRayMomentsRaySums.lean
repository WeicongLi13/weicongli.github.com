module

public import Cylinder.ExactRayMomentsActualBalance
public import Cylinder.ExactRayMomentsCanonicalTimes

/-! The actual finite white-fibre moments equal the sums in the manuscript's
canonical ray enumeration, with the same normalized product residues. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsRaySums
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsActualProduct
open Cylinder.ExactRayMomentsActualBalance Cylinder.ExactRayMomentsCanonicalTimes
open Cylinder.ExactRayMomentsLow
variable (p : ℕ) [Fact p.Prime]
local instance directionFintype : Fintype (BlackProjection.Direction p) := Fintype.ofFinite _

def whiteFibreEnumeration {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb) :
    Fin (BlackProjection.raySize p S b hb i) ≃
      {H : whitePoints p S // whiteDirection p hb H = i.val} :=
  (rayEnumeration (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) i).trans (whiteRayEquiv p hb i).symm

theorem whiteFibreEnumeration_value {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb)
    (ν : Fin (BlackProjection.raySize p S b hb i)) :
    (whiteFibreEnumeration p hb i ν).val = rayWhitePoint p hb i ν := rfl

theorem moment_eq_ray_sum {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : BlackProjection.directionSet p S b hb) (j : ℕ) :
    moment (whiteDirection p hb) (fun H => c H.val) (fun H => normalizedTime p b H.val) i.val j =
      ∑ ν : Fin (BlackProjection.raySize p S b hb i), c (rayWhitePoint p hb i ν).val *
        rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb) i ν ^ j := by
  unfold moment
  calc
    _ = ∑ H : {H : whitePoints p S // whiteDirection p hb H = i.val},
      c H.val.val * normalizedTime p b H.val.val ^ j :=
      Finset.sum_subtype _ (fun H => by simp) _
    _ = ∑ ν : Fin (BlackProjection.raySize p S b hb i),
      c (whiteFibreEnumeration p hb i ν).val.val *
        normalizedTime p b (whiteFibreEnumeration p hb i ν).val.val ^ j :=
      ((whiteFibreEnumeration p hb i).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [whiteFibreEnumeration_value, normalized_time_eq_rayTimes]

end Cylinder.ExactRayMomentsRaySums
end
