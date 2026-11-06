module

public import Cylinder.LaurentCoefficientLocalization
public import Cylinder.CoordinateTwistOverlap
public import Cylinder.PlaneLaurentTripleBasis

/-! The true localization at the product of the two affine
coordinates is an iterated Laurent polynomial ring. -/

@[expose] public section
noncomputable section
open scoped Classical AlgebraMonoidAlgebra

namespace Cylinder.TripleCoordinateLocalization

open MvPolynomial Cylinder.CoordinateLaurentLocalization
open Cylinder.PlaneLaurentOverlapBasis Cylinder.PlaneLaurentTripleBasis

set_option autoImplicit false

variable (K : Type*) [CommRing K]

abbrev coefficientRing := MvPolynomial (Fin 1) K
abbrev coefficientLocalization := Localization.Away (X 0 : coefficientRing K)
abbrev doubledRing := LaurentPolynomial (coefficientLocalization K)
abbrev productLocalization := Localization.Away ((X 0 : AffineRing K) * X 1)

instance coefficient_localized :
    IsLocalization.Away (LaurentPolynomial.C (X 0 : coefficientRing K)) (doubledRing K) :=
  LaurentCoefficientLocalization.target_isLocalization (coefficientRing K) (X 0)

def firstToDoubled : CoordinateTwistOverlap.affineLocalization K →ₐ[K] doubledRing K :=
  (IsScalarTower.toAlgHom K (overlapRing K) (doubledRing K)).comp
    (CoordinateTwistOverlap.localizationAlgEquiv K).toAlgHom

scoped instance firstAlgebra :
    Algebra (CoordinateTwistOverlap.affineLocalization K) (doubledRing K) :=
  (firstToDoubled K).toRingHom.toAlgebra

open scoped Cylinder.TripleCoordinateLocalization

scoped instance affineAlgebra : Algebra (AffineRing K) (doubledRing K) :=
  ((firstToDoubled K).toRingHom.comp
    (algebraMap (AffineRing K) (CoordinateTwistOverlap.affineLocalization K))).toAlgebra

scoped instance firstScalarTower :
    IsScalarTower (AffineRing K) (CoordinateTwistOverlap.affineLocalization K) (doubledRing K) :=
  IsScalarTower.of_algebraMap_eq' (R := AffineRing K)
    (S := CoordinateTwistOverlap.affineLocalization K) (A := doubledRing K) rfl

theorem secondCoordinate_image :
    CoordinateTwistOverlap.localizationEquiv K
      (algebraMap (AffineRing K) (CoordinateTwistOverlap.affineLocalization K) (X 1)) =
        LaurentPolynomial.C (X 0) := by
  rw [CoordinateTwistOverlap.localizationEquiv_algebraMap]
  change Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 (X (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.toLaurent_C]

theorem secondCoordinate_powers :
    (Submonoid.powers (algebraMap (AffineRing K)
      (CoordinateTwistOverlap.affineLocalization K) (X 1))).map
        (CoordinateTwistOverlap.localizationEquiv K).toMonoidHom =
          .powers (LaurentPolynomial.C (X 0 : coefficientRing K)) := by
  rw [Submonoid.map_powers]
  congr 1
  exact secondCoordinate_image K

instance first_localized :
    IsLocalization.Away (algebraMap (AffineRing K)
      (CoordinateTwistOverlap.affineLocalization K) (X 1)) (doubledRing K) :=
  IsLocalization.of_ringEquiv_left (CoordinateTwistOverlap.localizationEquiv K)
    (secondCoordinate_powers K) (fun _ => rfl)

instance product_localized :
    IsLocalization.Away ((X 0 : AffineRing K) * X 1) (doubledRing K) :=
  IsLocalization.Away.mul' (CoordinateTwistOverlap.affineLocalization K) (doubledRing K) (X 0) (X 1)

def productEquiv : productLocalization K ≃ₐ[AffineRing K] doubledRing K :=
  IsLocalization.algEquiv (.powers ((X 0 : AffineRing K) * X 1))
    (productLocalization K) (doubledRing K)

theorem coefficientPowersImage :
    (Submonoid.powers (X 0 : coefficientRing K)).map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toMonoidHom =
        .powers (Polynomial.X : Polynomial K) := by
  rw [Submonoid.map_powers]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv_apply]

def coefficientEquiv : coefficientLocalization K ≃+* LaurentPolynomial K :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (X 0 : coefficientRing K))
    (T := Submonoid.powers (Polynomial.X : Polynomial K))
    (coefficientLocalization K) (LaurentPolynomial K)
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv (coefficientPowersImage K)

theorem coefficientEquiv_algebraMap (p : coefficientRing K) :
    coefficientEquiv K (algebraMap (coefficientRing K) (coefficientLocalization K) p) =
      Polynomial.toLaurent (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S := coefficientLocalization K)
    (Q := LaurentPolynomial K) (coefficientPowersImage K) p

def coefficientAlgEquiv : coefficientLocalization K ≃ₐ[K] LaurentPolynomial K where
  __ := coefficientEquiv K
  commutes' a := by
    change coefficientEquiv K (algebraMap K (coefficientLocalization K) a) = _
    rw [IsScalarTower.algebraMap_apply K (coefficientRing K) (coefficientLocalization K),
      coefficientEquiv_algebraMap]
    change Polynomial.toLaurent (MvPolynomial.uniqueAlgEquiv K (Fin 1) (C a)) = _
    simp only [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_C, Polynomial.toLaurent_C]
    rfl

def doubledEquiv : doubledRing K ≃ₐ[K] tripleRing K :=
  AddMonoidAlgebra.mapAlgEquiv K ℤ (coefficientAlgEquiv K)

scoped instance coefficientScalarTower : IsScalarTower K (AffineRing K) (doubledRing K) := by
  apply IsScalarTower.of_algebraMap_eq' (R := K) (S := AffineRing K) (A := doubledRing K)
  apply RingHom.ext
  intro a
  change algebraMap K (doubledRing K) a = firstToDoubled K
    (algebraMap (AffineRing K) (CoordinateTwistOverlap.affineLocalization K)
      (algebraMap K (AffineRing K) a))
  rw [← IsScalarTower.algebraMap_apply K (AffineRing K)
    (CoordinateTwistOverlap.affineLocalization K)]
  exact ((firstToDoubled K).commutes a).symm

def productLaurentEquiv : productLocalization K ≃ₐ[K] tripleRing K :=
  ((productEquiv K).restrictScalars K).trans (doubledEquiv K)

def coefficientToLaurent : coefficientRing K →ₐ[K] LaurentPolynomial K :=
  (coefficientAlgEquiv K).toAlgHom.comp
    (IsScalarTower.toAlgHom K (coefficientRing K) (coefficientLocalization K))

theorem coefficientToLaurent_apply (p : coefficientRing K) :
    coefficientToLaurent K p = Polynomial.toLaurent (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) :=
  coefficientEquiv_algebraMap K p

def overlapToTriple : overlapRing K →ₐ[K] tripleRing K :=
  AddMonoidAlgebra.mapAlgHom ℤ (coefficientToLaurent K)

theorem overlapToTriple_coeff (p : overlapRing K) (d : ℤ) :
    (overlapToTriple K p).coeff d =
      Polynomial.toLaurent (MvPolynomial.uniqueAlgEquiv K (Fin 1) (p.coeff d)) := by
  rw [overlapToTriple, AddMonoidAlgebra.coeff_mapAlgHom, coefficientToLaurent_apply]

def firstToProduct : CoordinateTwistOverlap.affineLocalization K →+* productLocalization K :=
  IsLocalization.Away.awayToAwayRight (S := CoordinateTwistOverlap.affineLocalization K)
    (P := productLocalization K) (X 0 : AffineRing K) (X 1 : AffineRing K)

theorem firstToProduct_algebraMap (p : AffineRing K) :
    firstToProduct K (algebraMap (AffineRing K) (CoordinateTwistOverlap.affineLocalization K) p) =
      algebraMap (AffineRing K) (productLocalization K) p := by
  unfold firstToProduct IsLocalization.Away.awayToAwayRight
  exact IsLocalization.Away.lift_eq (S := CoordinateTwistOverlap.affineLocalization K)
    (g := algebraMap (AffineRing K) (productLocalization K)) (X 0 : AffineRing K) _ p

def firstToProductAlgHom :
    CoordinateTwistOverlap.affineLocalization K →ₐ[AffineRing K] productLocalization K where
  __ := firstToProduct K
  commutes' := firstToProduct_algebraMap K

theorem productEquiv_firstToProduct (p : CoordinateTwistOverlap.affineLocalization K) :
    productEquiv K (firstToProduct K p) = firstToDoubled K p := by
  have h : (productEquiv K).toRingHom.comp (firstToProduct K) =
      (firstToDoubled K).toRingHom := by
    apply IsLocalization.ringHom_ext (.powers (X 0 : AffineRing K))
    apply RingHom.ext
    intro q
    change productEquiv K (firstToProduct K (algebraMap (AffineRing K)
      (CoordinateTwistOverlap.affineLocalization K) q)) = _
    rw [firstToProduct_algebraMap, (productEquiv K).commutes]
    rfl
  exact congrArg (fun f => f p) h

theorem productLaurentEquiv_firstToProduct (p : CoordinateTwistOverlap.affineLocalization K) :
    productLaurentEquiv K (firstToProduct K p) =
      overlapToTriple K (CoordinateTwistOverlap.localizationAlgEquiv K p) := by
  change doubledEquiv K (productEquiv K (firstToProduct K p)) = _
  rw [productEquiv_firstToProduct]
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro d
  rfl

end Cylinder.TripleCoordinateLocalization

end
