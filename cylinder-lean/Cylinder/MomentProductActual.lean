module
public import Cylinder.MomentProductCoordinates
public import Cylinder.ArbitraryMomentData
@[expose] public section
noncomputable section
namespace Cylinder.MomentProductCoordinates
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ProjectionChart Cylinder.ExactRayMomentsDirections Cylinder.ExactRayMomentsLow
variable (p : ℕ) [Fact p.Prime] {b : DualPoint p}
theorem white_factor {S : Finset (Geometry.Point p)}
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (scale : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) :
    factor p C (ArbitraryMomentData.planeScale p hb scale β)
      (ExactRayMomentsCanonicalTimes.rayWhitePoint p hb i ν).val =
      actualFactor (directionForm (ArbitraryMomentData.direction p C hb scale i))
        (ArbitraryMomentData.time p C hb scale i ν) := by
  unfold factor
  rw [ArbitraryMomentData.actual_vector]
  rfl


end Cylinder.MomentProductCoordinates
end
