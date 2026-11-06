module

public import Cylinder.GlobalTwistAffineComparison
public import Cylinder.GlobalTwistStandardFractions

/-! The concrete local fraction module maps to actual sections of the
global twisting sheaf. A literal homogeneous fraction keeps its value at
every actual prime of the standard open. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistAffineFractions

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateTwistFractions Cylinder.GlobalTwistLocalFractions
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistAffineComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

def homogeneousFraction (v : ℤ) (m n : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) (hd : (m : ℤ) - n = v) : twistModule K v :=
  ⟨fractionLinear K n H, Submodule.subset_span ⟨m, n, H, hd, hH, rfl⟩⟩

theorem fractionModuleEquiv_homogeneousFraction (v : ℤ) (m n : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) (hd : (m : ℤ) - n = v) :
    fractionModuleEquiv K v (homogeneousFraction K v m n H hH hd) =
      HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) m H (by simpa using hH) := by
  apply (Cylinder.ProjectivePolynomialChart.chartEquiv K).injective
  rw [fractionModuleEquiv_apply, RingEquiv.apply_symm_apply,
    Cylinder.ProjectivePolynomialChart.chartEquiv_mk]
  exact Cylinder.CoordinateTwistTrivialization.chartEvaluation_fraction K n H

def fractionSection (v : ℤ) (z : twistModule K v) : Γ(twist K v, coordinateOpen K none) :=
  chartSectionEquiv K none v (coordinateOpen K none) le_rfl
    (Proj.awayToSection (grading K) (X none) (fractionModuleEquiv K v z))

theorem fractionSection_homogeneousFraction (v : ℤ) (m n : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) (hd : (m : ℤ) - n = v) (q : coordinateOpen K none) :
    (fractionSection K v (homogeneousFraction K v m n H hH hd)).val q =
      Localization.mk H ⟨X none ^ n,
        coordinate_power_avoids K none (coordinateOpen K none) le_rfl q n⟩ := by
  unfold fractionSection
  rw [fractionModuleEquiv_homogeneousFraction]
  exact GlobalTwistStandardFractions.chartSectionEquiv_fraction K none v m n H
    (by simpa using hH) hd q

end Cylinder.GlobalTwistAffineFractions
end
