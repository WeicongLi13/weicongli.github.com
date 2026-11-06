module

public import Cylinder.ProjectiveIntersectionSchemePoints
public import Cylinder.ProjectiveEquationGerms

/-! The Bezout length formula over every actual point of the projective
complete intersection. The two local equations are the germs of the
literal homogeneous-fraction sections F/Z^e and G/Z^t. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.ProjectiveSchemeBezout

open MvPolynomial Module AlgebraicGeometry
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.ProjectivePointInProj Cylinder.ProjectiveEquationGerms
open Cylinder.ProjectiveBezoutStalks Cylinder.ProjectiveIntersectionSchemePoints
open Cylinder.ProjectiveIntersectionPoints Cylinder.ProjectiveIntersectionLocalLengths
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation Cylinder.CurvePolarLocal
open Cylinder.ProjectiveCompleteIntersectionCover Cylinder.PlaneLineCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

theorem coordinates_mem (c : Chart K) (H : PlaneRing K) (n : ℕ) (hH : H.IsHomogeneous n) :
    c.coordinates H ∈ grading K (n • (1 : ℕ)) := by
  change (c.coordinates H).IsHomogeneous (n • (1 : ℕ))
  simpa [Chart.coordinates] using chartCoordinates_homogeneous c.a c.b c.ha c.hb H n hH

def fractionGerm (q : projectivePlane K) (hq : q ∈ standardOpen K) (n : ℕ)
    (H : HomogeneousPlanePolynomial (K := K)) (hH : H ∈ grading K (n • (1 : ℕ))) :
    (projectivePlane K).presheaf.stalk q :=
  (projectivePlane K).presheaf.germ (standardOpen K) q hq
    (Proj.awayToSection (grading K) (X none)
      (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n H hH))

omit [Infinite K] in
theorem commonZero_mem_standardOpen (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : SchemeCommonZero c F G) :
    q.val ∈ standardOpen K :=
  no_point_at_infinity c F G e t he ht hF hG hgood q.val q.property.1 q.property.2

def intersectionIdeal (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : SchemeCommonZero c F G) :
    Ideal ((projectivePlane K).presheaf.stalk q.val) :=
  Ideal.span ({
    fractionGerm K q.val (commonZero_mem_standardOpen K c F G e t he ht hF hG hgood q)
      e (c.coordinates F) (coordinates_mem K c F e hF),
    fractionGerm K q.val (commonZero_mem_standardOpen K c F G e t he ht hF hG hgood q)
      t (c.coordinates G) (coordinates_mem K c G t hG)} :
    Set ((projectivePlane K).presheaf.stalk q.val))

def localIntersectionLength (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : SchemeCommonZero c F G) : ℕ∞ :=
  Module.length ((projectivePlane K).presheaf.stalk q.val)
    (((projectivePlane K).presheaf.stalk q.val) ⧸
      intersectionIdeal K c F G e t he ht hF hG hgood q)

theorem local_length_at_ray (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : SchemeCommonZero c F G)
    (P : ProjectiveCommonZero F G) (hq : q.val = rayPoint (c.affinePoint P.val)) :
    localIntersectionLength K c F G e t he ht hF hG hgood q = originalLocalLength K c F G P := by
  rcases q with ⟨q, hqFG⟩
  dsimp only at hq
  subst q
  change Module.length (ProjectiveStalk K (c.affinePoint P.val))
    (ProjectiveStalk K (c.affinePoint P.val) ⧸ Ideal.span ({
      fractionGerm K (rayPoint (c.affinePoint P.val)) _ e (c.coordinates F) (coordinates_mem K c F e hF),
      fractionGerm K (rayPoint (c.affinePoint P.val)) _ t (c.coordinates G) (coordinates_mem K c G t hG)} :
        Set (ProjectiveStalk K (c.affinePoint P.val)))) = _
  unfold fractionGerm
  rw [← homogeneous_equations_germ_ideal]
  rfl

@[instance_reducible] def schemeCommonZeroFintype [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Fintype (SchemeCommonZero c F G) := by
  let := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  exact Fintype.ofEquiv (ProjectiveCommonZero F G)
    (canonicalEquiv c F G e t he ht hF hG hgood)

theorem sum_local_intersection_lengths [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := schemeCommonZeroFintype K c F G e t he ht hF hG hgood
    ∑ q : SchemeCommonZero c F G,
      localIntersectionLength K c F G e t he ht hF hG hgood q = (e * t : ℕ∞) := by
  let := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  let := schemeCommonZeroFintype K c F G e t he ht hF hG hgood
  rw [← Equiv.sum_comp (canonicalEquiv c F G e t he ht hF hG hgood)]
  have hl : ∀ P : ProjectiveCommonZero F G,
      localIntersectionLength K c F G e t he ht hF hG hgood
        (canonicalEquiv c F G e t he ht hF hG hgood P) = originalLocalLength K c F G P := by
    intro P
    apply local_length_at_ray
    exact canonicalEquiv_apply c F G e t he ht hF hG hgood P
  simp_rw [hl]
  exact sum_original_projective_stalk_lengths K c F G e t he ht hF hG hF0 hcop hgood

theorem bezout [IsAlgClosed K]
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := schemeCommonZeroFintype K c F G e t he ht hF hG hgood
      ∑ q : SchemeCommonZero c F G,
        localIntersectionLength K c F G e t he ht hF hG hgood q = (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, sum_local_intersection_lengths K c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.ProjectiveSchemeBezout
end
