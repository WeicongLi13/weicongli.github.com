module

public import Cylinder.GlobalTwistPairSections

/-! Every literal homogeneous coordinate fraction with denominator
supported on a pair of coordinates is an actual twisting-sheaf
section on that pairwise intersection. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistPairFractions

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame Cylinder.GlobalTwistPairSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem pairOpen_le_second (i j : Option (Fin 2)) : pairOpen K i j ≤ coordinateOpen K j :=
  ProjectiveSpectrum.basicOpen_mul_le_right (grading K) (X i) (X j)

theorem denominator_avoids (i j : Option (Fin 2)) (a b : ℕ) (q : pairOpen K i j) :
    X i ^ a * X j ^ b ∉ q.val.asHomogeneousIdeal :=
  q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
    (coordinate_power_avoids K i (pairOpen K i j) (pairOpen_le_first K i j) q a)
    (coordinate_power_avoids K j (pairOpen K i j) (pairOpen_le_second K i j) q b)

def fractionSection (i j : Option (Fin 2)) (v : ℤ) (d a b : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous d) (hd : (d : ℤ) - a - b = v) : Γ(twist K v, pairOpen K i j) := by
  refine ⟨fun q => (Localization.mk H ⟨X i ^ a * X j ^ b, denominator_avoids K i j a b q⟩ :
    FullLocal K q.val), ?_⟩
  change (isFractionPrelocal K v).sheafify.pred
    (fun q : pairOpen K i j => (Localization.mk H
      ⟨X i ^ a * X j ^ b, denominator_avoids K i j a b q⟩ : FullLocal K q.val))
  apply PrelocalPredicate.sheafifyOf
  exact ⟨d, a + b, H, X i ^ a * X j ^ b, by omega, hH,
    (isHomogeneous_X_pow i a).mul (isHomogeneous_X_pow j b),
    fun q => denominator_avoids K i j a b q, fun _ => rfl⟩

theorem fractionSection_value (i j : Option (Fin 2)) (v : ℤ) (d a b : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous d) (hd : (d : ℤ) - a - b = v) (q : pairOpen K i j) :
    (fractionSection K i j v d a b H hH hd).val q =
      Localization.mk H ⟨X i ^ a * X j ^ b, denominator_avoids K i j a b q⟩ := rfl

theorem fractionSection_restrict_value (i j : Option (Fin 2)) (v : ℤ) (d a b : ℕ)
    (H : PlaneRing K) (hH : H.IsHomogeneous d) (hd : (d : ℤ) - a - b = v)
    (U : (plane K).Opens) (hU : U ≤ pairOpen K i j) (q : U) :
    ((twist K v).presheaf.map (homOfLE hU).op
      (fractionSection K i j v d a b H hH hd)).val q =
      Localization.mk H
        ⟨X i ^ a * X j ^ b, denominator_avoids K i j a b ⟨q.val, hU q.property⟩⟩ := rfl

end Cylinder.GlobalTwistPairFractions

end
