module

public import Cylinder.CoordinateTwistOverlap
public import Cylinder.PlaneLaurentRestriction

/-! The actual overlap-section equivalence is linear over the
coefficient field, and actual sheaf restriction is the inclusion
of the previously constructed homogeneous Laurent pieces. -/

@[expose] public section
noncomputable section
open scoped Classical

universe u

namespace Cylinder.CoordinateTwistOverlapLinear

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistFractions
open Cylinder.CoordinateTwistChartModule Cylinder.CoordinateTwistLaurentPiece
open Cylinder.CoordinateTwistTrivialization Cylinder.CoordinateTwistOverlap
open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentChartBasis
open Cylinder.PlaneLaurentOverlapBasis Cylinder.PlaneLaurentRestriction

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] [Infinite K]

def coefficientMap : K →+* chartRing K :=
  (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm.toRingHom.comp MvPolynomial.C

theorem coefficientMap_fraction (a : K) :
    coefficientMap K a =
      HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) 0 (MvPolynomial.C a)
        (by simp) := by
  apply (Cylinder.ProjectivePolynomialChart.chartEquiv K).injective
  change Cylinder.ProjectivePolynomialChart.chartEquiv K
    ((Cylinder.ProjectivePolynomialChart.chartEquiv K).symm (MvPolynomial.C a)) = _
  rw [RingEquiv.apply_symm_apply, Cylinder.ProjectivePolynomialChart.chartEquiv_mk]
  simp

theorem coefficientMap_val (a : K) :
    (coefficientMap K a).val = algebraMap K (CoordinateLocalization K) a := by
  rw [coefficientMap_fraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change IsLocalization.mk' (CoordinateLocalization K) (MvPolynomial.C a) 1 = _
  rw [IsLocalization.mk'_one]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K) (CoordinateLocalization K) a).symm

scoped instance coefficientAlgebra : Algebra K (chartRing K) where
  toSMul := inferInstance
  algebraMap := coefficientMap K
  commutes' _ _ := mul_comm _ _
  smul_def' a x := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers (X none : PlaneRing K))
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, coefficientMap_val]
    exact Algebra.smul_def a x.val

open scoped Cylinder.CoordinateTwistOverlapLinear

theorem coefficientAlgebra_map (a : K) :
    algebraMap K (chartRing K) a =
      (Cylinder.ProjectivePolynomialChart.chartEquiv K).symm (MvPolynomial.C a) := rfl

theorem coefficientAlgebra_fraction (a : K) :
    algebraMap K (chartRing K) a =
      HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) 0 (MvPolynomial.C a)
        (by simp) := coefficientMap_fraction K a

scoped instance affineCoefficientTower : IsScalarTower K (chartRing K) (AffineRing K) := by
  apply IsScalarTower.of_algebraMap_eq' (R := K) (S := chartRing K) (A := AffineRing K)
  apply RingHom.ext
  intro a
  change MvPolynomial.C a = Cylinder.ProjectivePolynomialChart.chartEquiv K
    ((Cylinder.ProjectivePolynomialChart.chartEquiv K).symm (MvPolynomial.C a))
  rw [RingEquiv.apply_symm_apply]

scoped instance localizationCoefficientTower :
    IsScalarTower K (chartRing K) (affineLocalization K) := by
  apply IsScalarTower.of_algebraMap_eq'
    (R := K) (S := chartRing K) (A := affineLocalization K)
  apply RingHom.ext
  intro a
  rw [IsScalarTower.algebraMap_apply K (AffineRing K) (affineLocalization K)]
  change algebraMap (AffineRing K) (affineLocalization K) (MvPolynomial.C a) =
    algebraMap (AffineRing K) (affineLocalization K)
      (Cylinder.ProjectivePolynomialChart.chartEquiv K
        ((Cylinder.ProjectivePolynomialChart.chartEquiv K).symm (MvPolynomial.C a)))
  rw [RingEquiv.apply_symm_apply]

scoped instance sectionsKModule (v : ℤ) : Module K (overlapSections K v) :=
  Module.compHom _ (algebraMap K (chartRing K))

scoped instance sectionsKScalarTower (v : ℤ) :
    IsScalarTower K (chartRing K) (overlapSections K v) :=
  IsScalarTower.of_compHom K (chartRing K) (overlapSections K v)

def sectionLaurentLinearEquiv (v : ℤ) :
    overlapSections K v ≃ₗ[K] piece (K := K) v {0, 1} :=
  ((sectionLocalizationEquiv K v).restrictScalars K).trans
    ((CoordinateTwistOverlap.localizationAlgEquiv K).toLinearEquiv.trans
      (overlapLaurentEquiv v).symm)

theorem sectionLaurentLinearEquiv_apply (v : ℤ) (s : overlapSections K v) :
    sectionLaurentLinearEquiv K v s = sectionLaurentEquiv K v s := rfl

theorem chart_model_eq (v : ℤ) (z : twistModule K v) :
    localTwistLaurentEquiv K v (carrierEquiv K v z) =
      (chartPolynomialEquiv v).symm (twistAffineEquiv K v z) := by
  change (chartPolynomialEquiv v).symm
    ((affineWeightedEquiv K v).symm (twistLaurentEquiv K v (carrierEquiv K v z))) = _
  congr 1
  exact (evaluateOne_weighted K v (twistLaurentEquiv K v (carrierEquiv K v z))).symm

theorem restriction_as_piece_inclusion (v : ℤ) (z : twistModule K v) :
    sectionLaurentLinearEquiv K v (CoordinateTwistAffineSheaf.toOpen K v _ z) =
      chartInclusion v (localTwistLaurentEquiv K v (carrierEquiv K v z)) := by
  apply (overlapLaurentEquiv v).injective
  rw [sectionLaurentLinearEquiv_apply, sectionLaurentEquiv_restrict,
    chart_model_eq, chart_restriction, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
theorem global_restriction_as_piece_inclusion (v : ℤ) (z : twistModule K v) :
    sectionLaurentLinearEquiv K v
      ((modulesSpecToSheaf.obj (CoordinateTwistAffineSheaf.affineSheaf K v)).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen (overlapCoordinate K) ≤ ⊤ from le_top)).op
        (CoordinateTwistAffineSheaf.globalSectionsEquiv K v z)) =
      chartInclusion v (localTwistLaurentEquiv K v (carrierEquiv K v z)) := by
  have h := congrArg (fun f : CoordinateTwistAffineSheaf.moduleObject K v ⟶ overlapSections K v => f z)
    (CoordinateTwistAffineSheaf.toOpen_restrict K v ⊤
      (PrimeSpectrum.basicOpen (overlapCoordinate K)) (homOfLE le_top))
  change ((modulesSpecToSheaf.obj (CoordinateTwistAffineSheaf.affineSheaf K v)).presheaf.map
    (homOfLE le_top).op) (CoordinateTwistAffineSheaf.globalSectionsEquiv K v z) =
      CoordinateTwistAffineSheaf.toOpen K v _ z at h
  exact (congrArg (sectionLaurentLinearEquiv K v) h).trans
    (restriction_as_piece_inclusion K v z)

end Cylinder.CoordinateTwistOverlapLinear

end
