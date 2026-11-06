module

public import Cylinder.CompleteIntersectionPointBound
public import Cylinder.CompleteIntersectionSupport

/-! Actual interpolation on an irreducible plane curve, and cancellation
of evaluation relations supported on a lower-degree intersection. These
are the geometric zero and support steps of Theorem `thm:local`. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalCurveInterpolation

open Module MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.CompleteIntersectionPointBound
open Cylinder.CompleteIntersectionSupport
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem relPrime_of_lower_degree (F P : PlaneRing K) (e n : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (hne : n < e) : IsRelPrime F P := by
  apply hirr.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  have hdeg := totalDegree_le_of_dvd_of_isDomain hdiv hP0
  rw [hF.totalDegree hirr.ne_zero, hP.totalDegree hP0] at hdeg
  omega

/-- The true degree-product point bound includes a nonzero constant
second form, whose common point set is empty. -/
theorem curve_cardinal_bound (F P : PlaneRing K) (e n : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (hne : n < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hpoints : ∀ i, eval (v i) F = 0 ∧ eval (v i) P = 0) : Fintype.card I ≤ e * n := by
  by_cases hn : 0 < n
  · exact cardinal_bound F P e n (by omega) hn hF hP hirr.ne_zero
      (relPrime_of_lower_degree F P e n hF hirr hP hP0 hne) v hv hsep hpoints
  · have hn0 : n = 0 := by omega
    have hdeg : P.totalDegree = 0 := by simpa only [hn0] using hP.totalDegree hP0
    have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
    letI : IsEmpty I := ⟨fun i => by
      have hz : P.coeff 0 = 0 := by
        have hh := (hpoints i).2
        rw [hC, eval_C] at hh
        exact hh
      apply hP0
      rw [hC, hz, map_zero]⟩
    simp

/-- A lower-degree actual form vanishing at more than e*n actual
distinct points of the irreducible curve is the zero polynomial. -/
theorem polynomial_eq_zero_of_many_points (F P : PlaneRing K) (e n : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hP : P.IsHomogeneous n) (hne : n < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hpoints : ∀ i, eval (v i) F = 0 ∧ eval (v i) P = 0)
    (hcard : e * n < Fintype.card I) : P = 0 := by
  by_contra hP0
  have hbound := curve_cardinal_bound F P e n hF hirr hP hP0 hne v hv hsep hpoints
  omega

theorem zeros_in_subset_card_le (F A : PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hA : A.IsHomogeneous m) (hA0 : A ≠ 0) (hme : m < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) :
    (T.filter (fun i => eval (v i) A = 0)).card ≤ e * m := by
  let Z := T.filter (fun i => eval (v i) A = 0)
  have hz := curve_cardinal_bound F A e m hF hirr hA hA0 hme
    (fun i : Z => v i.val) (fun i => hv i.val)
    (by intro i j hij c; exact hsep i.val j.val (fun h => hij (Subtype.ext h)) c)
    (fun i => ⟨hFzero i.val, (Finset.mem_filter.mp i.property).2⟩)
  simpa only [Fintype.card_coe] using hz

/-- Removing actual zeros of the common denominator retains the point
threshold needed to force both cleared recurrences to be identities. -/
theorem recurrence_subset_after_denominator (F A : PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hA : A.IsHomogeneous m) (hA0 : A ≠ 0) (hme : m < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I)
    (hcard : e * (5 * m + 2) < T.card) :
    e * (4 * m + 2) < (T.filter (fun i => eval (v i) A ≠ 0)).card := by
  have hz := zeros_in_subset_card_le F A e m hF hirr hA hA0 hme v hv hsep hFzero T
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun i => eval (v i) A = 0)
  have hsum : (T.filter (fun i => eval (v i) A = 0)).card +
      (T.filter (fun i => eval (v i) A ≠ 0)).card = T.card := by
    simpa only [ne_eq] using hsplit
  have heq : e * (5 * m + 2) = e * m + e * (4 * m + 2) := by ring
  rw [heq] at hcard
  omega

/-- Cancellation at zeros of a lower-degree form is justified by actual
complete-intersection interpolation, including every zero of that form. -/
theorem relation_zero_of_supported_on_lower_curve (F A : PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hA : A.IsHomogeneous m) (hA0 : A ≠ 0) (hm : 0 < m) (hme : m < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (c : I → K) (d : ℕ)
    (hd : e + m - 2 ≤ d) (hrel : PowerEvaluationRelation.Relation v c d)
    (hsupport : ∀ i, eval (v i) A ≠ 0 → c i = 0) : c = 0 := by
  let Z := {i : I // eval (v i) A = 0}
  have hrelZ : PowerEvaluationRelation.Relation (fun i : Z => v i.val) (fun i => c i.val) d := by
    intro P hP
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : I => eval (v i) A = 0)
      (fun i => c i * eval (v i) P)
    have hout : (∑ i : {i : I // ¬eval (v i) A = 0}, c i.val * eval (v i.val) P) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hsupport i.val i.property, zero_mul]
    rw [hout, add_zero, hrel P hP] at hsplit
    exact hsplit
  have hind := independent_complete_intersection_representatives F A e m (by omega) hm hF hA hirr.ne_zero hA0
    (relPrime_of_lower_degree F A e m hF hirr hA hA0 hme)
    (fun i : Z => v i.val) (fun i => hv i.val)
    (by intro i j hij k; exact hsep i.val j.val (fun h => hij (Subtype.ext h)) k)
    (fun i => ⟨hFzero i.val, i.property⟩) d hd
  have hz := relation_eq_zero_of_independent (fun i : Z => v i.val) (fun i => c i.val) d hind hrelZ
  funext i
  by_cases hi : eval (v i) A = 0
  · exact congrFun hz ⟨i, hi⟩
  · exact hsupport i hi

#print axioms curve_cardinal_bound
#print axioms polynomial_eq_zero_of_many_points
#print axioms recurrence_subset_after_denominator
#print axioms relation_zero_of_supported_on_lower_curve

end Cylinder.LocalCurveInterpolation

end
