module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-! Localizing the coefficients of a Laurent polynomial ring is
the genuine localization at the corresponding constant Laurent
polynomial. This follows from the module-localization property of
finitely supported coefficient functions. -/

@[expose] public section
noncomputable section
open scoped Classical AlgebraMonoidAlgebra

namespace Cylinder.LaurentCoefficientLocalization

set_option autoImplicit false

variable (R : Type*) [CommRing R] (y : R)

abbrev coefficientRing := Localization.Away y
abbrev sourceRing := LaurentPolynomial R
abbrev targetRing := LaurentPolynomial (coefficientRing R y)

def coefficientMap : sourceRing R →ₗ[R] targetRing R y :=
  (IsScalarTower.toAlgHom R (sourceRing R) (targetRing R y)).toLinearMap

theorem coefficientMap_localized : IsLocalizedModule.Away y (coefficientMap R y) := by
  let f : R →ₗ[R] coefficientRing R y := Algebra.linearMap R (coefficientRing R y)
  let e₁ : sourceRing R ≃ₗ[R] (ℤ →₀ R) := AddMonoidAlgebra.coeffLinearEquiv R
  let e₂ : targetRing R y ≃ₗ[R] (ℤ →₀ coefficientRing R y) :=
    AddMonoidAlgebra.coeffLinearEquiv R
  have h₁ : IsLocalizedModule (.powers y)
      (e₂.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap (α := ℤ) f) :=
    IsLocalizedModule.of_linearEquiv (.powers y) (Finsupp.mapRange.linearMap f) e₂.symm
  have h₂ : IsLocalizedModule (.powers y)
      ((e₂.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap f) ∘ₗ e₁.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (.powers y) _ e₁
  convert h₂ using 1
  ext z n
  rfl

theorem target_isLocalization :
    IsLocalization.Away (LaurentPolynomial.C y) (targetRing R y) := by
  have h : IsLocalization
      (Algebra.algebraMapSubmonoid (sourceRing R) (.powers y)) (targetRing R y) :=
    isLocalizedModule_iff_isLocalization.mp (coefficientMap_localized R y)
  have he : Algebra.algebraMapSubmonoid (sourceRing R) (.powers y) =
      .powers (LaurentPolynomial.C y) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    rfl
  rwa [he] at h

theorem coefficientMap_apply (p : sourceRing R) (n : ℤ) :
    (coefficientMap R y p).coeff n = algebraMap R (coefficientRing R y) (p.coeff n) := rfl

end Cylinder.LaurentCoefficientLocalization

end
