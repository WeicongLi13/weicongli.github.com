module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.Basic

/-! An actual coordinate localization of the three-variable polynomial
ring is a Laurent polynomial ring over the other two variables. The
fraction and monomial formulas retain the original polynomial numerator
and denominator, for use in constructing local twisting modules. -/

@[expose] public section
noncomputable section

namespace Cylinder.CoordinateLaurentLocalization

set_option autoImplicit false

variable (K : Type*) [CommRing K]

abbrev PlaneRing := MvPolynomial (Option (Fin 2)) K
abbrev AffineRing := MvPolynomial (Fin 2) K
abbrev CoordinateLocalization := Localization.Away (MvPolynomial.X none : PlaneRing K)
abbrev LaurentChart := LaurentPolynomial (AffineRing K)

def coordinateEquiv : PlaneRing K ≃+* Polynomial (AffineRing K) :=
  (MvPolynomial.optionEquivLeft K (Fin 2)).toRingEquiv

theorem powers_image :
    (Submonoid.powers (MvPolynomial.X none : PlaneRing K)).map
      (coordinateEquiv K).toMonoidHom =
      Submonoid.powers (Polynomial.X : Polynomial (AffineRing K)) := by
  rw [Submonoid.map_powers]
  congr 1
  exact MvPolynomial.optionEquivLeft_X_none K (Fin 2)

/-- A true localization isomorphism, obtained from the universal property
of localization and the existing polynomial/Laurent localization. -/
def localizationEquiv : CoordinateLocalization K ≃+* LaurentChart K :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (MvPolynomial.X none : PlaneRing K))
    (T := Submonoid.powers (Polynomial.X : Polynomial (AffineRing K)))
    (CoordinateLocalization K) (LaurentChart K) (coordinateEquiv K) (powers_image K)

theorem localizationEquiv_algebraMap (p : PlaneRing K) :
    localizationEquiv K (algebraMap (PlaneRing K) (CoordinateLocalization K) p) =
      Polynomial.toLaurent (MvPolynomial.optionEquivLeft K (Fin 2) p) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq (S := CoordinateLocalization K)
    (Q := LaurentChart K) (powers_image K) p

theorem localizationEquiv_firstCoordinate :
    localizationEquiv K (algebraMap (PlaneRing K) (CoordinateLocalization K)
      (MvPolynomial.X none)) = LaurentPolynomial.T 1 := by
  rw [localizationEquiv_algebraMap, MvPolynomial.optionEquivLeft_X_none,
    Polynomial.toLaurent_X]

theorem localizationEquiv_otherCoordinate (i : Fin 2) :
    localizationEquiv K (algebraMap (PlaneRing K) (CoordinateLocalization K)
      (MvPolynomial.X (some i))) = LaurentPolynomial.C (MvPolynomial.X i) := by
  rw [localizationEquiv_algebraMap, MvPolynomial.optionEquivLeft_X_some,
    Polynomial.toLaurent_C]

theorem localizationEquiv_fraction (p : PlaneRing K) (n : ℕ) :
    localizationEquiv K (IsLocalization.mk' (CoordinateLocalization K) p
      (⟨MvPolynomial.X none ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X none : PlaneRing K))) =
      Polynomial.toLaurent (MvPolynomial.optionEquivLeft K (Fin 2) p) *
        LaurentPolynomial.T (-(n : ℤ)) := by
  rw [localizationEquiv, IsLocalization.ringEquivOfRingEquiv_mk']
  convert LaurentPolynomial.mk'_eq (MvPolynomial.optionEquivLeft K (Fin 2) p) n using 1
  congr 1
  apply Subtype.ext
  change MvPolynomial.optionEquivLeft K (Fin 2) (MvPolynomial.X none ^ n) = Polynomial.X ^ n
  rw [map_pow, MvPolynomial.optionEquivLeft_X_none]

/-- A monomial fraction becomes the corresponding actual Laurent
monomial. The exponent records the numerator degree minus the pole. -/
theorem localizationEquiv_monomialFraction (m : Option (Fin 2) →₀ ℕ) (a : K) (n : ℕ) :
    localizationEquiv K (IsLocalization.mk' (CoordinateLocalization K) (MvPolynomial.monomial m a)
      (⟨MvPolynomial.X none ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X none : PlaneRing K))) =
      LaurentPolynomial.C (MvPolynomial.monomial m.some a) *
        LaurentPolynomial.T ((m none : ℤ) - n) := by
  rw [localizationEquiv_fraction, MvPolynomial.optionEquivLeft_monomial,
    Polynomial.toLaurent_C_mul_T, mul_assoc, ← LaurentPolynomial.T_sub]

end Cylinder.CoordinateLaurentLocalization

end
