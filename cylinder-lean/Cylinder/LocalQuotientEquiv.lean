module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Length

/-! Localizing an actual quotient is the quotient of the ambient local
ring by the mapped ideal. The maximal ideal is transported by the actual
quotient map; no correspondence of local rings is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.LocalQuotientEquiv

variable (R : Type*) [CommRing R] (I : Ideal R)

abbrev preimageIdeal (m : MaximalSpectrum (R ⧸ I)) : Ideal R :=
  m.asIdeal.comap (Ideal.Quotient.mk I)

abbrev AmbientLocal (m : MaximalSpectrum (R ⧸ I)) :=
  Localization.AtPrime (preimageIdeal R I m)

abbrev AmbientLocalQuotient (m : MaximalSpectrum (R ⧸ I)) :=
  AmbientLocal R I m ⧸ I.map (algebraMap R (AmbientLocal R I m))

theorem image_primeCompl (m : MaximalSpectrum (R ⧸ I)) :
    Algebra.algebraMapSubmonoid (R ⧸ I) (preimageIdeal R I m).primeCompl =
      m.asIdeal.primeCompl :=
  Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective m.asIdeal

theorem ambientLocalQuotient_isLocalization (m : MaximalSpectrum (R ⧸ I)) :
    IsLocalization m.asIdeal.primeCompl (AmbientLocalQuotient R I m) := by
  rw [← image_primeCompl R I m]
  infer_instance

def quotientLocalizationEquiv (m : MaximalSpectrum (R ⧸ I)) :
    Localization.AtPrime m.asIdeal ≃ₐ[R ⧸ I] AmbientLocalQuotient R I m := by
  letI := ambientLocalQuotient_isLocalization R I m
  exact IsLocalization.algEquiv m.asIdeal.primeCompl _ _

theorem quotientLocalizationEquiv_apply (m : MaximalSpectrum (R ⧸ I)) (a : R ⧸ I) :
    quotientLocalizationEquiv R I m (algebraMap (R ⧸ I) (Localization.AtPrime m.asIdeal) a) =
      algebraMap (R ⧸ I) (AmbientLocalQuotient R I m) a :=
  (quotientLocalizationEquiv R I m).commutes a

theorem ambient_length_eq_quotient_length (m : MaximalSpectrum (R ⧸ I)) :
    Module.length (AmbientLocal R I m) (AmbientLocalQuotient R I m) =
      Module.length (AmbientLocalQuotient R I m) (AmbientLocalQuotient R I m) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

end Cylinder.LocalQuotientEquiv
end
