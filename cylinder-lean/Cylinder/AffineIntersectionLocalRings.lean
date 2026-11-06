module

public import Cylinder.AffineIntersectionPoints
public import Cylinder.LocalQuotientEquiv
public import Cylinder.RingLengthEquiv

/-! Actual local polynomial intersection rings at actual affine points.
Their ring isomorphism with local factors of the intersection algebra
comes from quotient-localization compatibility, rather than a length
definition or an assumed equality of dimensions. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.AffineIntersectionLocalRings

open MvPolynomial Module Cylinder.CompleteIntersectionKoszul Cylinder.AffineIntersectionPoints

variable {K σ : Type*} [Field K]

def pointIdeal (x : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (polynomialEvaluation x).toRingHom

instance pointIdeal_isMaximal (x : σ → K) : (pointIdeal x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)

abbrev PointLocal (x : σ → K) := Localization.AtPrime (pointIdeal x)

abbrev LocalIntersectionQuotient (f g : MvPolynomial σ K) (x : σ → K) :=
  PointLocal x ⧸ (equationsIdeal f g).map (algebraMap (MvPolynomial σ K) (PointLocal x))

theorem preimage_eq_pointIdeal (f g : MvPolynomial σ K) (x : CommonZero f g) :
    LocalQuotientEquiv.preimageIdeal (MvPolynomial σ K) (equationsIdeal f g)
      (toMaximalSpectrum f g x) = pointIdeal x.val := by
  ext P
  change eval x.val P = 0 ↔ eval x.val P = 0
  rfl

def localIntersectionEquiv (f g : MvPolynomial σ K) (x : CommonZero f g) :
    Localization.AtPrime (toMaximalSpectrum f g x).asIdeal ≃+*
      LocalIntersectionQuotient f g x.val :=
  (LocalQuotientEquiv.quotientLocalizationEquiv (MvPolynomial σ K) (equationsIdeal f g)
    (toMaximalSpectrum f g x)).toRingEquiv

theorem local_intersection_length (f g : MvPolynomial σ K) (x : CommonZero f g) :
    Module.length (PointLocal x.val) (LocalIntersectionQuotient f g x.val) =
      Module.length (Localization.AtPrime (toMaximalSpectrum f g x).asIdeal)
        (Localization.AtPrime (toMaximalSpectrum f g x).asIdeal) := by
  have hs : Function.Surjective
      (algebraMap (PointLocal x.val) (LocalIntersectionQuotient f g x.val)) :=
    Ideal.Quotient.mk_surjective
  exact (Module.length_eq_of_surjective (R := LocalIntersectionQuotient f g x.val)
    (M := LocalIntersectionQuotient f g x.val) hs).trans
      (RingLengthEquiv.self_length_eq (localIntersectionEquiv f g x)).symm

theorem mapped_equations (f g : MvPolynomial σ K) (x : σ → K) :
    (equationsIdeal f g).map (algebraMap (MvPolynomial σ K) (PointLocal x)) =
      Ideal.span ({algebraMap (MvPolynomial σ K) (PointLocal x) f,
        algebraMap (MvPolynomial σ K) (PointLocal x) g} : Set (PointLocal x)) := by
  simp [equationsIdeal, Ideal.map_span]

end Cylinder.AffineIntersectionLocalRings
end
