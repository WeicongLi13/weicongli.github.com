module

public import Cylinder.CoordinateTwistTrivialization
public import Cylinder.PlaneLaurentOverlapBasis
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! Actual sections on the intersection of the first two standard
coordinate opens are identified with a true Laurent localization.
The section-restriction formula follows from the universal property
of module localization. -/

@[expose] public section
noncomputable section
open scoped Classical

universe u

namespace Cylinder.CoordinateTwistOverlap

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateTwistTrivialization Cylinder.PlaneLaurentOverlapBasis
open Cylinder.PlaneLaurentPieces

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u)

section Ring

variable [CommRing K]

abbrev affineLocalization := Localization.Away (X 0 : AffineRing K)

theorem affinePowersImage :
    (Submonoid.powers (X 0 : AffineRing K)).map (MvPolynomial.finSuccEquiv K 1).toMonoidHom =
      Submonoid.powers (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)) := by
  rw [Submonoid.map_powers]
  congr 1
  exact finSuccEquiv_X_zero

def localizationEquiv : affineLocalization K ≃+* overlapRing K :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (X 0 : AffineRing K))
    (T := Submonoid.powers (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)))
    (affineLocalization K) (overlapRing K) (MvPolynomial.finSuccEquiv K 1).toRingEquiv (affinePowersImage K)

theorem localizationEquiv_algebraMap (p : AffineRing K) :
    localizationEquiv K (algebraMap (AffineRing K) (affineLocalization K) p) =
      Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 p) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S := affineLocalization K)
    (Q := overlapRing K) (affinePowersImage K) p

def localizationAlgEquiv : affineLocalization K ≃ₐ[K] overlapRing K where
  __ := localizationEquiv K
  commutes' a := by
    change localizationEquiv K (algebraMap K (affineLocalization K) a) =
      algebraMap K (overlapRing K) a
    rw [IsScalarTower.algebraMap_apply K (AffineRing K) (affineLocalization K),
      localizationEquiv_algebraMap]
    change Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C a)) = _
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, Polynomial.toLaurent_C]
    rfl

def overlapCoordinate : chartRing K :=
  HomogeneousLocalization.Away.isLocalizationElem (coordinate_mem K)
    (show (X (some 0) : PlaneRing K) ∈ grading K 1 from isHomogeneous_X K (some 0))

theorem overlap_preimage :
    Proj.awayι (grading K) (X none) (coordinate_mem K) zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (grading K) (X (some 0)) =
        PrimeSpectrum.basicOpen (overlapCoordinate K) :=
  Proj.awayι_preimage_basicOpen (grading K) (coordinate_mem K) zero_lt_one
    (show (X (some 0) : PlaneRing K) ∈ grading K 1 from isHomogeneous_X K (some 0))
    zero_lt_one

end Ring

section Field

variable [Field K] [Infinite K]

theorem overlapCoordinate_toAffine :
    Cylinder.ProjectivePolynomialChart.chartEquiv K (overlapCoordinate K) = X 0 := by
  rw [overlapCoordinate, Cylinder.ProjectivePolynomialChart.chartEquiv_mk]
  simp

instance localizationScalarTower :
    IsScalarTower (chartRing K) (AffineRing K) (affineLocalization K) := by
  infer_instance

def affineLocalizationMap : AffineRing K →ₗ[chartRing K] affineLocalization K :=
  (Algebra.linearMap (AffineRing K) (affineLocalization K)).restrictScalars (chartRing K)

instance affineLocalizationMap_localized :
    IsLocalizedModule.Away (overlapCoordinate K) (affineLocalizationMap K) := by
  have : IsLocalizedModule
      (.powers (algebraMap (chartRing K) (AffineRing K) (overlapCoordinate K)))
      (Algebra.linearMap (AffineRing K) (affineLocalization K)) := by
    rw [affineAlgebra_map, overlapCoordinate_toAffine]
    infer_instance
  exact IsLocalizedModule.restrictScalars_powers (overlapCoordinate K)
    (Algebra.linearMap (AffineRing K) (affineLocalization K))

def twistLocalizationMap (v : ℤ) : twistModule K v →ₗ[chartRing K] affineLocalization K :=
  (affineLocalizationMap K).comp (twistAffineEquiv K v).toLinearMap

instance twistLocalizationMap_localized (v : ℤ) :
    IsLocalizedModule.Away (overlapCoordinate K) (twistLocalizationMap K v) :=
  IsLocalizedModule.of_linearEquiv_right (.powers (overlapCoordinate K))
    (affineLocalizationMap K) (twistAffineEquiv K v)

abbrev overlapSections (v : ℤ) : ModuleCat.{u} (chartRing K) :=
  (modulesSpecToSheaf.obj (Cylinder.CoordinateTwistAffineSheaf.affineSheaf K v)).presheaf.obj
    (op (PrimeSpectrum.basicOpen (overlapCoordinate K)))

set_option backward.isDefEq.respectTransparency false in
def sectionLocalizationEquiv (v : ℤ) :
    overlapSections K v ≃ₗ[chartRing K] affineLocalization K := by
  letI : IsLocalizedModule.Away (overlapCoordinate K) (twistLocalizationMap K v) :=
    twistLocalizationMap_localized K v
  exact IsLocalizedModule.linearEquiv (.powers (overlapCoordinate K))
    (Cylinder.CoordinateTwistAffineSheaf.toOpen K v _).hom (twistLocalizationMap K v)

set_option backward.isDefEq.respectTransparency false in
theorem sectionLocalizationEquiv_restrict (v : ℤ) (z : twistModule K v) :
    sectionLocalizationEquiv K v
      (Cylinder.CoordinateTwistAffineSheaf.toOpen K v _ z) =
        algebraMap (AffineRing K) (affineLocalization K) (twistAffineEquiv K v z) := by
  let : IsLocalizedModule.Away (overlapCoordinate K) (twistLocalizationMap K v) :=
    twistLocalizationMap_localized K v
  exact IsLocalizedModule.linearEquiv_apply (.powers (overlapCoordinate K))
    (Cylinder.CoordinateTwistAffineSheaf.toOpen K v _).hom (twistLocalizationMap K v) z

def sectionLaurentEquiv (v : ℤ) : overlapSections K v ≃+ piece (K := K) v {0, 1} :=
  (sectionLocalizationEquiv K v).toAddEquiv.trans
    ((localizationAlgEquiv K).toAddEquiv.trans (overlapLaurentEquiv v).symm.toAddEquiv)

theorem sectionLaurentEquiv_restrict (v : ℤ) (z : twistModule K v) :
    overlapLaurentEquiv v
      (sectionLaurentEquiv K v (Cylinder.CoordinateTwistAffineSheaf.toOpen K v _ z)) =
        Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 (twistAffineEquiv K v z)) := by
  change overlapLaurentEquiv v ((overlapLaurentEquiv v).symm
    (localizationAlgEquiv K (sectionLocalizationEquiv K v
      (Cylinder.CoordinateTwistAffineSheaf.toOpen K v _ z)))) = _
  rw [LinearEquiv.apply_symm_apply, sectionLocalizationEquiv_restrict]
  exact localizationEquiv_algebraMap K _

end Field

end Cylinder.CoordinateTwistOverlap

end
