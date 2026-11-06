module

public import Cylinder.ProjectiveRayStalk

/-! Bezout's length formula in actual projective-plane structure-sheaf
stalks. Local equations are the dehomogenized original homogeneous
equations, pulled back through the actual standard affine chart. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.ProjectiveBezoutStalks

open MvPolynomial Module AlgebraicGeometry
open Cylinder.ProjectiveAffineOpen Cylinder.ProjectivePointInProj Cylinder.ProjectiveRayStalk
open Cylinder.AffineAmbientStalkQuotient Cylinder.AffineIntersectionLocalRings
open Cylinder.ProjectiveIntersectionPoints Cylinder.ProjectiveIntersectionLocalLengths
open Cylinder.CompleteIntersectionKoszul Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.CurvePolarLocal

variable (K : Type*) [Field K] [Infinite K]

abbrev ProjectiveStalk (x : Fin 2 → K) :=
  (projectivePlane K).presheaf.stalk (rayPoint x)

def polynomialGerm (x : Fin 2 → K) : MvPolynomial (Fin 2) K →+* ProjectiveStalk K x :=
  (canonicalStalkEquiv K x).symm.toRingHom.comp
    (algebraMap (MvPolynomial (Fin 2) K) (AmbientStalk x))

theorem polynomialGerm_apply (x : Fin 2 → K) (f : MvPolynomial (Fin 2) K) :
    canonicalStalkEquiv K x (polynomialGerm K x f) =
      algebraMap (MvPolynomial (Fin 2) K) (AmbientStalk x) f :=
  (canonicalStalkEquiv K x).apply_symm_apply _

def germIdeal (f g : MvPolynomial (Fin 2) K) (x : Fin 2 → K) : Ideal (ProjectiveStalk K x) :=
  Ideal.span ({polynomialGerm K x f, polynomialGerm K x g} : Set (ProjectiveStalk K x))

abbrev ProjectiveStalkQuotient (f g : MvPolynomial (Fin 2) K) (x : Fin 2 → K) :=
  ProjectiveStalk K x ⧸ germIdeal K f g x

def stalkQuotientEquiv (f g : MvPolynomial (Fin 2) K) (x : Fin 2 → K) :
    ProjectiveStalkQuotient K f g x ≃+* StalkIntersectionQuotient f g x := by
  apply Ideal.quotientEquiv _ _ (canonicalStalkEquiv K x)
  simp only [germIdeal, Ideal.map_span, Set.image_pair]
  change _ = Ideal.span ({canonicalStalkEquiv K x (polynomialGerm K x f),
    canonicalStalkEquiv K x (polynomialGerm K x g)} : Set (AmbientStalk x))
  rw [polynomialGerm_apply, polynomialGerm_apply]
  simp only [polynomial_map_is_germ]
  exact stalk_mapped_equations f g x

theorem projective_stalk_quotient_length (f g : MvPolynomial (Fin 2) K) (x : Fin 2 → K) :
    Module.length (ProjectiveStalk K x) (ProjectiveStalkQuotient K f g x) =
      Module.length (AmbientStalk x) (StalkIntersectionQuotient f g x) := by
  have hs : Function.Surjective
      (algebraMap (ProjectiveStalk K x) (ProjectiveStalkQuotient K f g x)) := Ideal.Quotient.mk_surjective
  have ha : Function.Surjective
      (algebraMap (AmbientStalk x) (StalkIntersectionQuotient f g x)) := Ideal.Quotient.mk_surjective
  exact (Module.length_eq_of_surjective (R := ProjectiveStalkQuotient K f g x)
    (M := ProjectiveStalkQuotient K f g x) hs).trans
      ((RingLengthEquiv.self_length_eq (stalkQuotientEquiv K f g x)).trans
        (Module.length_eq_of_surjective (R := StalkIntersectionQuotient f g x)
          (M := StalkIntersectionQuotient f g x) ha).symm)

def equationGerm (x : Fin 2 → K) (H : HomogeneousPlanePolynomial (K := K)) : ProjectiveStalk K x :=
  polynomialGerm K x (dehomogenize H)

def originalLocalLength (c : Chart K) (F G : PlaneRing K) (P : ProjectiveCommonZero F G) : ℕ∞ :=
  Module.length (ProjectiveStalk K (c.affinePoint P.val))
    (ProjectiveStalkQuotient K (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))
      (c.affinePoint P.val))

theorem original_equations_ideal (c : Chart K) (F G : PlaneRing K) (P : ProjectiveCommonZero F G) :
    germIdeal K (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G)) (c.affinePoint P.val) =
      Ideal.span ({equationGerm K (c.affinePoint P.val) (c.coordinates F),
        equationGerm K (c.affinePoint P.val) (c.coordinates G)} :
          Set (ProjectiveStalk K (c.affinePoint P.val))) := rfl

theorem originalLocalLength_eq (c : Chart K) (F G : PlaneRing K) (P : ProjectiveCommonZero F G) :
    originalLocalLength K c F G P = projectiveAmbientLength c F G P :=
  projective_stalk_quotient_length K _ _ _

theorem sum_original_projective_stalk_lengths [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
    ∑ P : ProjectiveCommonZero F G, originalLocalLength K c F G P = (e * t : ℕ∞) := by
  let := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  simp_rw [originalLocalLength_eq]
  exact sum_projective_ambient_stalk_lengths c F G e t he ht hF hG hF0 hcop hgood

theorem bezout_local_length_formula [IsAlgClosed K]
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
      ∑ P : ProjectiveCommonZero F G, originalLocalLength K c F G P = (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, sum_original_projective_stalk_lengths K c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.ProjectiveBezoutStalks
end
