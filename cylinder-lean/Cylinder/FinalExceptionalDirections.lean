module

public import Cylinder.DirectionCurveProposition
public import Cylinder.CompleteIntersectionSupport
public import Cylinder.MinimalDependentSubset
public import Cylinder.PlaneRelationSpaces
public import Mathlib.RingTheory.Coprime.Lemmas

/-! Independence of the directions supporting at least three white points,
as in the current manuscript's exceptional-direction lemma. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalExceptionalDirections

open MvPolynomial Module Finset
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.MinimalEvaluationRelation Cylinder.MinimalDependentSubset

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

/-- A small subset of a curve is independent when every curve below the
threshold is coprime to the containing equation. The proof uses a genuine
minimal dependent subset, complete-intersection interpolation, and the
proved numerical-character bound. -/
theorem small_subset_independent
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (T : Finset I) (F : PlaneRing K) (s t d : ℕ)
    (hs : 0 < s) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ i, eval (v i) F = 0)
    (hsmall : T.card < t * (d + 3 - t))
    (hdegree : s + t ≤ d + 3)
    (hcop : ∀ G : PlaneRing K, ∀ r < t, G.IsHomogeneous r → G ≠ 0 → IsRelPrime F G) :
    Function.Surjective (evaluationMap (fun i : T => v i.val) d) := by
  by_contra hdep
  obtain ⟨W, hWT, hmin⟩ := exists_minimally_dependent_subset v T d hdep
  let w : W → Fin 3 → K := fun i => v i.val
  have hw : ∀ i, w i ≠ 0 := fun i => hv i.val
  have hwsep : ProjectivelyDistinct w := by
    intro i k hik a
    exact hsep i.val k.val (fun h => hik (Subtype.ext h)) a
  let : Nonempty W := minimally_dependent_nonempty w d hmin
  obtain ⟨r, hr⟩ := InitialDegreeExists.exists_initialDegree w
  have hrt : t ≤ r := by
    by_contra hbad
    have hrt' : r < t := by omega
    obtain ⟨G, hG, hG0, hGzero⟩ :=
      (Cylinder.EquationScalarDescent.idealPiece_ne_bot_iff w r).mp hr.1
    have hr0 := initialDegree_pos w r hr
    have hind := CompleteIntersectionSupport.independent_complete_intersection_representatives
      F G s r hs hr0 hF hG hF0 hG0 (hcop G r hrt' hG hG0) w hw hwsep
      (fun i => ⟨hzero i.val, hGzero i⟩) d (by omega)
    exact hmin.1 ((InitialDegreeExists.independent_iff_surjective w d).mp hind)
  have hb := (ActualCharacterBounds.minimally_dependent_character_bounds
    w hw hwsep r hr d hmin).2.2.2 t hrt
  have hcard : Fintype.card W ≤ T.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hWT
  omega

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.RationalPlanePointModel

/-- The exceptional rays of the actual black-point projection are independent
in degree `(p-5)/2`, without assuming the main cylinder theorem. -/
theorem exceptional_directions_independent (p : ℕ) [Fact p.Prime]
    (hp : 11 ≤ p) {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    Function.Surjective (evaluationMap
      (fun i : DirectionExcess.largeRays p S b hb =>
        representatives (embedding p) (directionSet p S b hb) i.val) ((p - 5) / 2)) := by
  let D := directionSet p S b hb
  let v := representatives (embedding p) D
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree v
  obtain ⟨hlo, hhi, hkl, hkn, hkp, F, hF, hF0, hzero, hsq, hsqmap, habs, hfactor⟩ :=
    DirectionCurveProposition.direction_curve p hp hcard hS hnon hb s hs
  let t := (p - 2 * s + 1) / 2
  let d := (p - 5) / 2
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := hpodd
  have hdelta : p - 2 * s + 1 = 2 * t := by dsimp [t]; omega
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hpst : p + 1 = 2 * s + 2 * t := by omega
  have hd : d + 3 = s + t := by dsimp [d]; omega
  have hspos : 0 < s := by unfold DirectionExcess.threshold at hlo; omega
  have hslarge : 2 * t ≤ s := by
    obtain ⟨P⟩ := DirectionCurveBounds.direction_nonempty p hcard hS hnon hb
    obtain ⟨Q, hQ, _⟩ := (PlaneCurveFactors.eval_zero_iff_factor_zero F hF0 P.val.rep).mp
      (hzero P.val P.property)
    have hQlo := hfactor Q hQ
    have hQhi := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      (PlaneCurveFactors.factor_dvd F Q hQ) hF0
    rw [hF.totalDegree hF0] at hQhi
    omega
  have hwhite := SimpleBlackWeights.white_card_exact p hcard hS hnon
  have hlarge := DirectionExcess.large_rays_card_le_excess p hb
  rw [DirectionExcess.ray_excess_identity p hcard hS hb] at hlarge
  have htwice := DirectionCurveBounds.twice_direction_card_le_white p hcard hS hb
  have hcount : (DirectionExcess.largeRays p S b hb).card < s * t := by
    have hsub : p - s + s = p := by omega
    have hoddprod : 2 * (p * (p - 1) / 2) = p * (p - 1) := by
      have hpminus : p - 1 = 2 * a := by omega
      have hmul : p * (p - 1) = 2 * (p * a) := by rw [hpminus]; ring
      omega
    have hp1 : p - 1 + 1 = p := by omega
    have hlarge' : (DirectionExcess.largeRays p S b hb).card +
        2 * D.card ≤ 1 + p * (p - 1) / 2 := by
      change 2 * D.card ≤ (whitePoints p S).card at htwice
      change _ ≤ (whitePoints p S).card - 2 * D.card at hlarge
      omega
    have hsbound : 2 * t * t ≤ s * t := Nat.mul_le_mul_right t hslarge
    change s * (p - s) ≤ D.card at hkl
    have hps := congrArg (fun n : ℕ => n * s) hpst
    have hpt := congrArg (fun n : ℕ => n * t) hpst
    have hpp := congrArg (fun n : ℕ => n * p) hpst
    have hsubmul := congrArg (fun n : ℕ => s * n) hsub
    have hpmul := congrArg (fun n : ℕ => p * n) hp1
    nlinarith
  let M := MvPolynomial.map (embedding p) F
  have hM : M.IsHomogeneous s := hF.map (embedding p)
  have hM0 : M ≠ 0 := by
    intro hz
    exact hF0 (MvPolynomial.map_injective (embedding p) (embedding p).injective
      (by simpa only [map_zero] using hz))
  have hMzero : ∀ i : D, eval (v i) M = 0 := by
    intro i
    change eval (fun j => embedding p (i.val.rep j)) (MvPolynomial.map (embedding p) F) = 0
    calc
      _ = embedding p (eval i.val.rep F) := (MvPolynomial.map_eval (embedding p) i.val.rep F).symm
      _ = 0 := by rw [hzero i.val i.property, map_zero]
  have hcop : ∀ G : PlaneRing (CurveField p), ∀ r < t,
      G.IsHomogeneous r → G ≠ 0 → IsRelPrime M G := by
    intro G r hrt hG hG0
    have hprod : IsRelPrime (∏ Q ∈ PlaneCurveFactors.factors F,
        MvPolynomial.map (embedding p) Q) G := by
      apply IsRelPrime.prod_left
      intro Q hQ
      apply (habs Q hQ).isRelPrime_iff_not_dvd.mpr
      intro hdiv
      have hQ0 := (habs Q hQ).ne_zero
      have hQhom := (PlaneCurveFactors.factor_homogeneous F s hF hF0 Q hQ).map (embedding p)
      have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hG0
      rw [hQhom.totalDegree hQ0, hG.totalDegree hG0] at hdeg
      have hbound := hfactor Q hQ
      omega
    have hMdiv : M ∣ ∏ Q ∈ PlaneCurveFactors.factors F, MvPolynomial.map (embedding p) Q := by
      obtain ⟨R, hR⟩ := (MinimumEquationComponentSets.factors_product_associated F hF0 hsq).symm.dvd
      refine ⟨MvPolynomial.map (embedding p) R, ?_⟩
      rw [← map_prod, hR, map_mul]
    intro Q hQM hQG
    exact hprod (hQM.trans hMdiv) hQG
  apply small_subset_independent v (representatives_nonzero _ D) (representatives_distinct _ D)
    (DirectionExcess.largeRays p S b hb) M s t d hspos hM hM0 hMzero
  · simpa only [hd, Nat.add_sub_cancel, mul_comm s t] using hcount
  · omega
  · exact hcop

theorem exceptional_direction_relation_space_eq_bot (p : ℕ) [Fact p.Prime]
    (hp : 11 ≤ p) {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    PlaneRelationSpaces.relationSpace
      (fun i : DirectionExcess.largeRays p S b hb =>
        representatives (embedding p) (directionSet p S b hb) i.val) ((p - 5) / 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  rw [Submodule.mem_bot]
  apply _root_.funext
  exact GapRelations.relation_zero_of_surjective _ c _
    (exceptional_directions_independent p hp hcard hS hnon hb)
    ((PlaneRelationSpaces.mem_relationSpace _ _ c).mp hc)

#print axioms small_subset_independent
#print axioms exceptional_directions_independent
#print axioms exceptional_direction_relation_space_eq_bot

end Cylinder.FinalExceptionalDirections

end
