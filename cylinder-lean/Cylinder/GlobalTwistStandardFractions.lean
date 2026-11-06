module

public import Cylinder.GlobalTwistChartFrame

/-! The standard coordinate frames preserve the literal homogeneous
fractions H/X_i^n, including negative twists. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistStandardFractions

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem frame_mul_fraction (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (m n : ℕ) (H : PlaneRing K)
    (hd : (m : ℤ) - n = v) (q : U) :
    (frame K i v U hU).val q *
        Localization.mk H ⟨X i ^ m, coordinate_power_avoids K i U hU q m⟩ =
      Localization.mk H ⟨X i ^ n, coordinate_power_avoids K i U hU q n⟩ := by
  have he : v.toNat + n = (-v).toNat + m := by omega
  rw [frame_apply, Localization.mk_mul]
  simp only [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq']
  apply congrArg (algebraMap (PlaneRing K) (FullLocal K q.val))
  change (X i ^ v.toNat * H) * X i ^ n = H * (X i ^ (-v).toNat * X i ^ m)
  calc
    _ = H * (X i ^ v.toNat * X i ^ n) := by ring
    _ = H * X i ^ (v.toNat + n) := by rw [pow_add]
    _ = H * X i ^ ((-v).toNat + m) := by rw [he]
    _ = _ := by rw [pow_add]

theorem away_mk_section_value (i : Option (Fin 2)) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (1 : ℕ))) (q : coordinateOpen K i) :
    ((Proj.awayToSection (grading K) (X i)
        (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH)).val q).val =
      Localization.mk H ⟨X i ^ m,
        coordinate_power_avoids K i (coordinateOpen K i) le_rfl q m⟩ := by
  refine (ProjectiveSpectrum.Proj.awayToSection_apply (grading K) (X i)
    (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH) q).trans ?_
  rw [HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk'_apply, IsLocalization.map_mk']
  rw [Localization.mk_eq_mk'_apply]
  exact congrArg
    (fun b : q.val.asHomogeneousIdeal.toIdeal.primeCompl =>
      IsLocalization.mk' (FullLocal K q.val) H b) (Subtype.ext rfl)

theorem chartSectionEquiv_fraction (i : Option (Fin 2)) (v : ℤ) (m n : ℕ)
    (H : PlaneRing K) (hH : H ∈ grading K (m • (1 : ℕ)))
    (hd : (m : ℤ) - n = v) (q : coordinateOpen K i) :
    (chartSectionEquiv K i v (coordinateOpen K i) le_rfl
        (Proj.awayToSection (grading K) (X i)
          (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH))).val q =
      Localization.mk H ⟨X i ^ n,
        coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩ := by
  rw [chartSectionEquiv_apply, away_mk_section_value]
  exact frame_mul_fraction K i v (coordinateOpen K i) le_rfl m n H hd q

end Cylinder.GlobalTwistStandardFractions
end
