module

public import Cylinder.OriginalProjectiveGerms

/-! Bezout's formula in the original three homogeneous coordinates:
every point is an actual point of the original projective scheme, and
each summand is the length of its actual ambient stalk modulo the two
germs F/L^e and G/L^t in a common avoiding chart. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.OriginalSchemeBezout

open MvPolynomial Module AlgebraicGeometry
open Cylinder.ProjectiveCoordinateIso Cylinder.OriginalProjectiveGerms
open Cylinder.ProjectiveIntersectionSchemePoints Cylinder.ProjectiveChartData
open Cylinder.HilbertEvaluation Cylinder.CurvePolarLocal

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

abbrev OriginalCommonZero (F G : PlaneRing K) :=
  {q : originalPlane K // F ∈ q.asHomogeneousIdeal ∧ G ∈ q.asHomogeneousIdeal}

def zeroEquiv (c : Chart K) (F G : PlaneRing K) :
    SchemeCommonZero c F G ≃ OriginalCommonZero K F G :=
  Equiv.subtypeEquiv (coordinateIso c).hom.homeomorph.toEquiv
    (fun q => ((membership c q F).and (membership c q G)).symm)

omit [Infinite K] in
theorem zeroEquiv_apply_val (c : Chart K) (F G : PlaneRing K) (q : SchemeCommonZero c F G) :
    (zeroEquiv K c F G q).val = (coordinateIso c).hom q.val := rfl

omit [Infinite K] in
theorem original_mem_chart (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (P : OriginalCommonZero K F G) :
    P.val ∈ Proj.basicOpen (originalGrading K) (chartLinearForm K c) := by
  let q := (zeroEquiv K c F G).symm P
  have heq : (coordinateIso c).hom q.val = P.val :=
    congrArg (fun R : OriginalCommonZero K F G => R.val) ((zeroEquiv K c F G).apply_symm_apply P)
  rw [← heq]
  exact chart_point_mem K c q.val
    (ProjectiveSchemeBezout.commonZero_mem_standardOpen K c F G e t he ht hF hG hgood q)

def intersectionIdeal (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (P : OriginalCommonZero K F G) :
    Ideal ((originalPlane K).presheaf.stalk P.val) :=
  Ideal.span ({
    originalFractionGerm K (chartLinearForm K c) (chartLinearForm_mem K c) P.val
      (original_mem_chart K c F G e t he ht hF hG hgood P) e F (by simpa using hF),
    originalFractionGerm K (chartLinearForm K c) (chartLinearForm_mem K c) P.val
      (original_mem_chart K c F G e t he ht hF hG hgood P) t G (by simpa using hG)} :
    Set ((originalPlane K).presheaf.stalk P.val))

def localIntersectionLength (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (P : OriginalCommonZero K F G) : ℕ∞ :=
  Module.length ((originalPlane K).presheaf.stalk P.val)
    (((originalPlane K).presheaf.stalk P.val) ⧸ intersectionIdeal K c F G e t he ht hF hG hgood P)

theorem local_length_eq (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : SchemeCommonZero c F G) :
    localIntersectionLength K c F G e t he ht hF hG hgood (zeroEquiv K c F G q) =
      ProjectiveSchemeBezout.localIntersectionLength K c F G e t he ht hF hG hgood q := by
  let E := stalkEquiv c q.val
  let I := intersectionIdeal K c F G e t he ht hF hG hgood (zeroEquiv K c F G q)
  let J := ProjectiveSchemeBezout.intersectionIdeal K c F G e t he ht hF hG hgood q
  have hIJ : I.map E.toRingHom = J := by
    simp only [I, J, intersectionIdeal, ProjectiveSchemeBezout.intersectionIdeal,
      Ideal.map_span, Set.image_pair]
    change Ideal.span ({
      stalkEquiv c q.val (originalFractionGerm K (chartLinearForm K c) (chartLinearForm_mem K c)
        ((coordinateIso c).hom q.val) _ e F (by simpa using hF)),
      stalkEquiv c q.val (originalFractionGerm K (chartLinearForm K c) (chartLinearForm_mem K c)
        ((coordinateIso c).hom q.val) _ t G (by simpa using hG))} :
      Set ((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val)) = _
    have hqchart := ProjectiveSchemeBezout.commonZero_mem_standardOpen K c F G e t he ht hF hG hgood q
    rw [chart_fractionGerm_map K c q.val hqchart e F hF,
      chart_fractionGerm_map K c q.val hqchart t G hG]
  let EQ : (((originalPlane K).presheaf.stalk ((coordinateIso c).hom q.val)) ⧸ I) ≃+*
      (((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val) ⧸ J) :=
    Ideal.quotientEquiv I J E hIJ.symm
  have hs : Function.Surjective
      (algebraMap ((originalPlane K).presheaf.stalk ((coordinateIso c).hom q.val))
        (((originalPlane K).presheaf.stalk ((coordinateIso c).hom q.val)) ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  have htgt : Function.Surjective
      (algebraMap ((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val)
        (((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val) ⧸ J)) :=
    Ideal.Quotient.mk_surjective
  exact (Module.length_eq_of_surjective (R :=
    (((originalPlane K).presheaf.stalk ((coordinateIso c).hom q.val)) ⧸ I))
      (M := (((originalPlane K).presheaf.stalk ((coordinateIso c).hom q.val)) ⧸ I)) hs).trans
      ((RingLengthEquiv.self_length_eq EQ).trans
        (Module.length_eq_of_surjective (R :=
          (((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val) ⧸ J))
          (M := (((ProjectiveAffineOpen.projectivePlane K).presheaf.stalk q.val) ⧸ J)) htgt).symm)

@[instance_reducible] def originalCommonZeroFintype [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Fintype (OriginalCommonZero K F G) := by
  let := ProjectiveSchemeBezout.schemeCommonZeroFintype K c F G e t he ht hF hG hgood
  exact Fintype.ofEquiv (SchemeCommonZero c F G) (zeroEquiv K c F G)

theorem sum_local_intersection_lengths [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := originalCommonZeroFintype K c F G e t he ht hF hG hgood
    ∑ P : OriginalCommonZero K F G,
      localIntersectionLength K c F G e t he ht hF hG hgood P = (e * t : ℕ∞) := by
  let := ProjectiveSchemeBezout.schemeCommonZeroFintype K c F G e t he ht hF hG hgood
  let := originalCommonZeroFintype K c F G e t he ht hF hG hgood
  rw [← Equiv.sum_comp (zeroEquiv K c F G)]
  simp_rw [local_length_eq]
  exact ProjectiveSchemeBezout.sum_local_intersection_lengths K c F G e t he ht hF hG hF0 hcop hgood

theorem bezout [IsAlgClosed K]
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := originalCommonZeroFintype K c F G e t he ht hF hG hgood
      ∑ P : OriginalCommonZero K F G,
        localIntersectionLength K c F G e t he ht hF hG hgood P = (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, sum_local_intersection_lengths K c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.OriginalSchemeBezout
end
