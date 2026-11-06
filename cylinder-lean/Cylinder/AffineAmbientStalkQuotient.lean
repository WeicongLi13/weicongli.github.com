module

public import Cylinder.ProjectiveIntersectionLocalLengths
public import Cylinder.AffineIntersectionStalkLengths

/-! Local intersection quotients in the actual structure-sheaf stalk
of the affine ambient plane. The polynomial map is the actual germ map,
and its images of the equations generate the stalk ideal. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

namespace Cylinder.AffineAmbientStalkQuotient

open MvPolynomial Module AlgebraicGeometry CategoryTheory
open Cylinder.CompleteIntersectionKoszul Cylinder.AffineIntersectionLocalRings
open Cylinder.ProjectiveIntersectionPoints Cylinder.ProjectiveIntersectionLocalLengths
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation Cylinder.CurvePolarLocal

variable {K σ : Type*} [Field K]

def pointPrime (x : σ → K) : PrimeSpectrum (MvPolynomial σ K) :=
  ⟨pointIdeal x, inferInstance⟩

abbrev AmbientStalk (x : σ → K) :=
  AffineIntersectionStalkLengths.stalkRing (MvPolynomial σ K) (pointPrime x)

instance ambientStalkAlgebra (x : σ → K) : Algebra (MvPolynomial σ K) (AmbientStalk x) :=
  (StructureSheaf.toStalk (MvPolynomial σ K) (pointPrime x)).hom.toAlgebra

def ambientStalkEquiv (x : σ → K) : AmbientStalk x ≃ₐ[MvPolynomial σ K] PointLocal x :=
  (StructureSheaf.stalkIso (MvPolynomial σ K) (pointPrime x)).symm

theorem polynomial_map_is_germ (x : σ → K) (P : MvPolynomial σ K) :
    algebraMap (MvPolynomial σ K) (AmbientStalk x) P =
      StructureSheaf.toStalk (MvPolynomial σ K) (pointPrime x) P := rfl

abbrev StalkIntersectionQuotient (f g : MvPolynomial σ K) (x : σ → K) :=
  AmbientStalk x ⧸ (equationsIdeal f g).map
    (algebraMap (MvPolynomial σ K) (AmbientStalk x))

def stalkQuotientEquiv (f g : MvPolynomial σ K) (x : σ → K) :
    StalkIntersectionQuotient f g x ≃+* LocalIntersectionQuotient f g x := by
  let e := ambientStalkEquiv x
  apply Ideal.quotientEquiv _ _ e.toRingEquiv
  rw [Ideal.map_map]
  have he : (e.toRingEquiv : AmbientStalk x →+* PointLocal x).comp
      (algebraMap (MvPolynomial σ K) (AmbientStalk x)) =
      algebraMap (MvPolynomial σ K) (PointLocal x) := by
    apply RingHom.ext
    intro P
    exact e.commutes P
  exact congrArg (fun h : MvPolynomial σ K →+* PointLocal x => Ideal.map h (equationsIdeal f g)) he.symm

theorem stalk_mapped_equations (f g : MvPolynomial σ K) (x : σ → K) :
    (equationsIdeal f g).map (algebraMap (MvPolynomial σ K) (AmbientStalk x)) =
      Ideal.span ({StructureSheaf.toStalk (MvPolynomial σ K) (pointPrime x) f,
        StructureSheaf.toStalk (MvPolynomial σ K) (pointPrime x) g} : Set (AmbientStalk x)) := by
  simp only [equationsIdeal, Ideal.map_span, Set.image_pair, polynomial_map_is_germ]
  rfl

theorem ambient_stalk_quotient_length (f g : MvPolynomial σ K) (x : σ → K) :
    Module.length (AmbientStalk x) (StalkIntersectionQuotient f g x) =
      Module.length (PointLocal x) (LocalIntersectionQuotient f g x) := by
  have hs : Function.Surjective (algebraMap (AmbientStalk x) (StalkIntersectionQuotient f g x)) :=
    Ideal.Quotient.mk_surjective
  have hl : Function.Surjective (algebraMap (PointLocal x) (LocalIntersectionQuotient f g x)) :=
    Ideal.Quotient.mk_surjective
  exact (Module.length_eq_of_surjective (R := StalkIntersectionQuotient f g x)
    (M := StalkIntersectionQuotient f g x) hs).trans
      ((RingLengthEquiv.self_length_eq (stalkQuotientEquiv f g x)).trans
        (Module.length_eq_of_surjective (R := LocalIntersectionQuotient f g x)
          (M := LocalIntersectionQuotient f g x) hl).symm)

def projectiveAmbientLength (c : Chart K) (F G : PlaneRing K) (P : ProjectiveCommonZero F G) : ℕ∞ :=
  Module.length (AmbientStalk (c.affinePoint P.val))
    (StalkIntersectionQuotient (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))
      (c.affinePoint P.val))

theorem projectiveAmbientLength_eq (c : Chart K) (F G : PlaneRing K)
    (P : ProjectiveCommonZero F G) :
    projectiveAmbientLength c F G P = localIntersectionLength c F G P :=
  ambient_stalk_quotient_length _ _ _

theorem sum_projective_ambient_stalk_lengths [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
    ∑ P : ProjectiveCommonZero F G, projectiveAmbientLength c F G P = (e * t : ℕ∞) := by
  let := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  simp_rw [projectiveAmbientLength_eq]
  exact sum_projective_local_lengths c F G e t he ht hF hG hF0 hcop hgood

end Cylinder.AffineAmbientStalkQuotient
end
