module

public import Cylinder.GlobalTwistCoordinateSections

/-! Every actual section on a standard projective chart has a single
homogeneous numerator and a power of that chart coordinate as denominator.
This follows from the actual chart equivalence, for every integer twist. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistCoordinateFractionRepresentatives

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame Cylinder.GlobalTwistCoordinateSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem exists_coordinate_fraction (i : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K i)) :
    ∃ (m n : ℕ) (H : PlaneRing K), H.IsHomogeneous m ∧ (m : ℤ) - n = v ∧
      ∀ q : coordinateOpen K i, s.val q = Localization.mk H
        ⟨X i ^ n, coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩ := by
  obtain ⟨c, rfl⟩ := (sectionLinearEquiv K i v).surjective s
  obtain ⟨k, H, hH, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading K) (isHomogeneous_X K i) c
  refine ⟨v.toNat + k, (-v).toNat + k, X i ^ v.toNat * H, ?_, by omega, ?_⟩
  · exact (isHomogeneous_X_pow i v.toNat).mul (by simpa using hH)
  · intro q
    change (frame K i v (coordinateOpen K i) le_rfl).val q *
      ((Proj.awayToSection (grading K) (X i)
        (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) k H hH)).val q).val = _
    rw [GlobalTwistStandardFractions.away_mk_section_value, frame_apply, Localization.mk_mul]
    exact congrArg (Localization.mk (X i ^ v.toNat * H))
      (Subtype.ext (pow_add (X i) (-v).toNat k).symm)

end Cylinder.GlobalTwistCoordinateFractionRepresentatives
end
