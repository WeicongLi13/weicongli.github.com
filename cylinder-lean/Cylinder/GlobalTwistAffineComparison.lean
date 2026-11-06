module

public import Cylinder.GlobalTwistChartSheaf
public import Cylinder.CoordinateTwistTrivialization

/-! The restriction of the global twisting sheaf to the first standard
chart is isomorphic to the genuine tilde sheaf of the original homogeneous
fraction module. Both trivializations use the same coordinate frame. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistAffineComparison

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

def affineToChart : AffineRing K ≃ₗ[chartRing K] chartRing K where
  __ := (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm.toAddEquiv
  map_smul' c x := by
    change (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm
      (Cylinder.ProjectivePolynomialChart.chartEquiv K c * x) =
        c * (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm x
    rw [map_mul, RingEquiv.symm_apply_apply]

def fractionModuleEquiv (v : ℤ) : twistModule K v ≃ₗ[chartRing K] chartRing K :=
  (Cylinder.CoordinateTwistTrivialization.twistAffineEquiv K v).trans (affineToChart K)

theorem fractionModuleEquiv_apply (v : ℤ) (z : twistModule K v) :
    fractionModuleEquiv K v z =
      (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm
        (Cylinder.CoordinateTwistTrivialization.chartEvaluation K z.val) := rfl

def affineSheafTrivialization (v : ℤ) :
    Cylinder.CoordinateTwistAffineSheaf.affineSheaf K v ≅
      SheafOfModules.unit (Cylinder.CoordinateTwistAffineSheaf.coordinateSpec K).ringCatSheaf :=
  (AlgebraicGeometry.tilde.functor (CommRingCat.of (chartRing K))).mapIso
      (fractionModuleEquiv K v).toModuleIso ≪≫
    AlgebraicGeometry.tildeSelf

def localSheafTrivialization (v : ℤ) :
    Cylinder.CoordinateTwistAffineSheaf.standardOpenSheaf K v ≅
      SheafOfModules.unit (Cylinder.CoordinateTwistAffineSheaf.standardOpen K).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (Cylinder.CoordinateTwistAffineSheaf.standardOpenIso K).hom).mapIso
      (affineSheafTrivialization K v) ≪≫
    Scheme.Modules.restrictUnitIso (Cylinder.CoordinateTwistAffineSheaf.standardOpenIso K).hom

def standardChartIso (v : ℤ) :
    (twist K v).restrict (Cylinder.CoordinateTwistAffineSheaf.standardOpen K).ι ≅
      Cylinder.CoordinateTwistAffineSheaf.standardOpenSheaf K v :=
  GlobalTwistChartSheaf.chartTrivialization K none v ≪≫
    (localSheafTrivialization K v).symm

end Cylinder.GlobalTwistAffineComparison
end
