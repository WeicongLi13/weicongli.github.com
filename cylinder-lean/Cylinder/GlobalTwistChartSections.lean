module

public import Cylinder.GlobalTwistAffineFractions
public import Cylinder.GlobalTwistKSheaf
public import Cylinder.CoordinateTwistOverlapLinear

/-! Actual sections of the global twisting sheaf on the first standard
chart are the original fraction module, with its original K-action. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistChartSections

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateTwistFractions Cylinder.GlobalTwistLocalFractions
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistAffineComparison Cylinder.GlobalTwistAffineFractions

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

scoped instance fractionKModule (v : ℤ) : Module K (twistModule K v) :=
  inferInstanceAs (Module K (twistPiece K v))

scoped instance actualSectionKModule (v : ℤ) (U : (plane K).Opens) :
    Module K Γ(twist K v, U) :=
  inferInstanceAs (Module K (sectionsSubmodule K v U))

open scoped Cylinder.GlobalTwistChartSections

def sectionEquiv (v : ℤ) : twistModule K v ≃ Γ(twist K v, coordinateOpen K none) :=
  (fractionModuleEquiv K v).toEquiv.trans
    ((Iso.commRingCatIsoToRingEquiv
      (Proj.basicOpenIsoAway (grading K) (X none) (coordinate_mem K) zero_lt_one)).toEquiv.trans
        (chartSectionEquiv K none v (coordinateOpen K none) le_rfl).toEquiv)

theorem sectionEquiv_apply (v : ℤ) (z : twistModule K v) :
    sectionEquiv K v z = fractionSection K v z := rfl

theorem fractionSection_add (v : ℤ) (z w : twistModule K v) :
    fractionSection K v (z + w) = fractionSection K v z + fractionSection K v w := by
  unfold fractionSection
  rw [map_add, map_add, map_add]

theorem fractionModule_smul (v : ℤ) (a : K) (z : twistModule K v) :
    fractionModuleEquiv K v (a • z) =
      Cylinder.CoordinateTwistOverlapLinear.coefficientMap K a * fractionModuleEquiv K v z := by
  have he : a • z = Cylinder.CoordinateTwistOverlapLinear.coefficientMap K a • z := by
    apply Subtype.ext
    change a • z.val = _
    rw [twistModule_smul_coe, HomogeneousLocalization.algebraMap_apply,
      Cylinder.CoordinateTwistOverlapLinear.coefficientMap_val]
    exact Algebra.smul_def a z.val
  rw [he, map_smul]
  rfl

theorem away_coefficient_value (a : K) (q : coordinateOpen K none) :
    ((Proj.awayToSection (grading K) (X none)
      (Cylinder.CoordinateTwistOverlapLinear.coefficientMap K a)).val q).val =
        algebraMap K (FullLocal K q.val) a := by
  rw [Cylinder.CoordinateTwistOverlapLinear.coefficientMap_fraction]
  have he := GlobalTwistStandardFractions.away_mk_section_value K none 0 (C a) (by simp) q
  refine he.trans ?_
  change Localization.mk (C a) (1 : q.val.asHomogeneousIdeal.toIdeal.primeCompl) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K) (FullLocal K q.val) a).symm

theorem fractionSection_smul (v : ℤ) (a : K) (z : twistModule K v) :
    fractionSection K v (a • z) = a • fractionSection K v z := by
  apply Subtype.ext
  funext q
  change (frame K none v (coordinateOpen K none) le_rfl).val q *
    ((Proj.awayToSection (grading K) (X none) (fractionModuleEquiv K v (a • z))).val q).val =
      a • ((frame K none v (coordinateOpen K none) le_rfl).val q *
        ((Proj.awayToSection (grading K) (X none) (fractionModuleEquiv K v z)).val q).val)
  rw [fractionModule_smul, map_mul, AlgebraicGeometry.Proj.mul_apply,
    HomogeneousLocalization.val_mul, away_coefficient_value, Algebra.smul_def]
  exact mul_left_comm _ _ _

def sectionLinearEquiv (v : ℤ) :
    twistModule K v ≃ₗ[K] Γ(twist K v, coordinateOpen K none) where
  __ := sectionEquiv K v
  map_add' := fractionSection_add K v
  map_smul' := fractionSection_smul K v

theorem sectionLinearEquiv_apply (v : ℤ) (z : twistModule K v) :
    sectionLinearEquiv K v z = fractionSection K v z := rfl

end Cylinder.GlobalTwistChartSections
end
