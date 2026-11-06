module

public import Cylinder.ProjectivePolynomialChart
public import Cylinder.AffineIntersectionStalkLengths
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! The genuine standard affine open of the projective plane and the
induced isomorphism of structure-sheaf stalks. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveAffineOpen

open AlgebraicGeometry CategoryTheory MvPolynomial
open Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open Cylinder.ProjectivePolynomialChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

abbrev projectivePlane : Scheme := Proj (grading K)

abbrev standardOpen : (projectivePlane K).Opens :=
  Proj.basicOpen (grading K) (X none)

def affineOpenIso : (standardOpen K).toScheme ≅ Spec (CommRingCat.of (PlanePolynomial (K := K))) :=
  Proj.basicOpenIsoSpec (grading K) (X none) (coordinate_mem K) zero_lt_one ≪≫
    Scheme.Spec.mapIso (chartEquiv K).symm.toCommRingCatIso.op

def affineEmbedding : Spec (CommRingCat.of (PlanePolynomial (K := K))) ⟶ projectivePlane K :=
  (affineOpenIso K).inv ≫ (standardOpen K).ι

instance affineEmbedding_isOpenImmersion : IsOpenImmersion (affineEmbedding K) := by
  unfold affineEmbedding
  infer_instance

def affinePoint (p : PrimeSpectrum (PlanePolynomial (K := K))) : projectivePlane K :=
  affineEmbedding K p

def stalkEquiv (p : PrimeSpectrum (PlanePolynomial (K := K))) :
    (projectivePlane K).presheaf.stalk (affinePoint K p) ≃+*
      AffineIntersectionStalkLengths.stalkRing (PlanePolynomial (K := K)) p := by
  haveI : IsIso ((affineEmbedding K).stalkMap p) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (affineEmbedding_isOpenImmersion K)).2 p
  exact (asIso ((affineEmbedding K).stalkMap p)).commRingCatIsoToRingEquiv

theorem stalkEquiv_apply (p : PrimeSpectrum (PlanePolynomial (K := K)))
    (a : (projectivePlane K).presheaf.stalk (affinePoint K p)) :
    stalkEquiv K p a = (affineEmbedding K).stalkMap p a := rfl

end Cylinder.ProjectiveAffineOpen

end
