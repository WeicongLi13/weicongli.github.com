module

public import Cylinder.DirectionComponentDecomposition
public import Cylinder.GlobalMomentSupport

/-! Actual pair cofactors and the support of the cleared component difference. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentCofactors

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneCurveFactors Cylinder.MinimumEquationComponentSets
open Cylinder.DirectionComponentDecomposition

variable {K L : Type*} [Field K] [Field L]

def pairCofactor (F G Q : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  ∏ R ∈ ((factors F).erase G).erase Q, R

theorem pair_factor_degree_remainder (F G Q : MvPolynomial (Fin 3) K) (s : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hsq : Squarefree F)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q) :
    s - G.totalDegree - Q.totalDegree + G.totalDegree + Q.totalDegree = s := by
  have hdegrees := factors_degree_sum_eq F hF0 hsq
  rw [hF.totalDegree hF0] at hdegrees
  have hsumG := Finset.add_sum_erase (factors F) (fun R => R.totalDegree) hG
  have hsumQ := Finset.add_sum_erase ((factors F).erase G) (fun R => R.totalDegree)
    (Finset.mem_erase.mpr ⟨hGQ.symm, hQ⟩)
  omega

theorem pairCofactor_homogeneous (F G Q : MvPolynomial (Fin 3) K) (s : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hsq : Squarefree F)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q) :
    (pairCofactor F G Q).IsHomogeneous (s - G.totalDegree - Q.totalDegree) := by
  have hhom := IsHomogeneous.prod (((factors F).erase G).erase Q) (fun R => R)
    (fun R => R.totalDegree) (fun R hR => factor_homogeneous F s hF hF0 R
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR)))
  have hdegrees := factors_degree_sum_eq F hF0 hsq
  rw [hF.totalDegree hF0] at hdegrees
  have hsumG := Finset.add_sum_erase (factors F) (fun R => R.totalDegree) hG
  have hsumQ := Finset.add_sum_erase ((factors F).erase G) (fun R => R.totalDegree)
    (Finset.mem_erase.mpr ⟨hGQ.symm, hQ⟩)
  have heq : (∑ R ∈ ((factors F).erase G).erase Q, R.totalDegree) =
      s - G.totalDegree - Q.totalDegree := by omega
  rw [heq] at hhom
  exact hhom

theorem pairCofactor_ne_zero (F G Q : MvPolynomial (Fin 3) K) : pairCofactor F G Q ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro R hR
  exact (factor_irreducible F R (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR))).ne_zero

theorem pairCofactor_nonzero_on_component (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (P : PlanePoint K)
    (hP : P ∈ componentPoints D F G) : eval P.rep (pairCofactor F G Q) ≠ 0 := by
  rw [pairCofactor, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro R hR
  exact (Finset.mem_filter.mp hP).2.2 R (Finset.mem_of_mem_erase hR)

theorem nonzero_pairCofactor_off_first_component (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) (P : PlanePoint K) (hPD : P ∈ D)
    (hH : eval P.rep (pairCofactor F G Q) ≠ 0) (hPG : eval P.rep G ≠ 0) :
    P ∈ componentPoints D F Q := by
  have hothers : ∀ R ∈ ((factors F).erase G).erase Q, eval P.rep R ≠ 0 := by
    rw [pairCofactor, map_prod, Finset.prod_ne_zero_iff] at hH
    exact hH
  obtain ⟨R, hR, hRzero⟩ := (eval_zero_iff_factor_zero F hF0 P.rep).mp (hzero P hPD)
  have hRQ : R = Q := by
    by_contra hRQ
    have hRG : R ≠ G := by intro h; exact hPG (h ▸ hRzero)
    exact hothers R (Finset.mem_erase.mpr ⟨hRQ, Finset.mem_erase.mpr ⟨hRG, hR⟩⟩) hRzero
  refine Finset.mem_filter.mpr ⟨hPD, hRQ ▸ hRzero, ?_⟩
  intro R hR
  by_cases hRG : R = G
  · exact hRG ▸ hPG
  · exact hothers R (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hR).1,
      Finset.mem_erase.mpr ⟨hRG, (Finset.mem_erase.mp hR).2⟩⟩)

theorem zero_on_factor_mem_component_or_intersection (D : Finset (PlanePoint K))
    (F G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) (P : PlanePoint K)
    (hPD : P ∈ D) (hPG : eval P.rep G = 0) :
    P ∈ componentPoints D F G ∪ intersectionPoints D F := by
  by_cases hPJ : P ∈ intersectionPoints D F
  · exact Finset.mem_union_right _ hPJ
  · have hPunion : P ∈ exclusiveUnion D F := by
      by_contra hn
      exact hPJ (Finset.mem_sdiff.mpr ⟨hPD, hn⟩)
    obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hPunion
    have hQG : Q = G := by
      by_contra hQG
      exact (Finset.mem_filter.mp hPQ).2.2 G (Finset.mem_erase.mpr ⟨Ne.symm hQG, hG⟩) hPG
    exact Finset.mem_union_left _ (hQG ▸ hPQ)

def clearedDifference (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (m u : D → L) (q : MvPolynomial (Fin 3) L) : D → L :=
  fun P => f (eval P.val.rep (pairCofactor F G Q)) *
    (m P - eval (representatives f D P) q * u P)

theorem clearedDifference_relation (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (s d a : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hsq : Squarefree F)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q)
    (m u : D → L) (q : MvPolynomial (Fin 3) L) (hq : q.IsHomogeneous a)
    (had : a ≤ d) (hHd : s - G.totalDegree - Q.totalDegree ≤ d - a)
    (hu : PowerEvaluationRelation.Relation (representatives f D) u d)
    (hm : PowerEvaluationRelation.Relation (representatives f D) m (d - a)) :
    PowerEvaluationRelation.Relation (representatives f D)
      (clearedDifference f D F G Q m u q) (d - a - (s - G.totalDegree - Q.totalDegree)) := by
  have hqu := GlobalMomentSupport.relation_after_polynomial_multiplication
    (representatives f D) u d a had q hq hu
  have hqu' : PowerEvaluationRelation.Relation (representatives f D)
      (fun P => eval (representatives f D P) q * u P) (d - a) := by
    simpa only [mul_comm] using hqu
  have hdiff := GlobalMomentSupport.relation_sub (representatives f D) m _ (d - a) hm hqu'
  have hmult := GlobalMomentSupport.relation_after_polynomial_multiplication (representatives f D)
    (fun P => m P - eval (representatives f D P) q * u P) (d - a)
    (s - G.totalDegree - Q.totalDegree) hHd (MvPolynomial.map f (pairCofactor F G Q))
    ((pairCofactor_homogeneous F G Q s hF hF0 hsq hG hQ hGQ).map f) hdiff
  convert hmult using 1
  funext P
  rw [MinimumEquationComponents.eval_mapped_cofactor]
  exact mul_comm _ _

theorem clearedDifference_support_on_first_factor (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (m u : D → L) (q : MvPolynomial (Fin 3) L)
    (hidentity : ∀ P : D, P.val ∈ componentPoints D F Q →
      m P = eval (representatives f D P) q * u P) :
    ∀ P : D, clearedDifference f D F G Q m u q P ≠ 0 →
      eval (representatives f D P) (MvPolynomial.map f G) = 0 ∧
      P.val ∈ componentPoints D F G ∪ intersectionPoints D F := by
  intro P hP
  have hH : eval P.val.rep (pairCofactor F G Q) ≠ 0 := by
    intro hz
    apply hP
    simp only [clearedDifference, hz, map_zero, zero_mul]
  have hPG : eval P.val.rep G = 0 := by
    by_contra hPG
    have hPQ := nonzero_pairCofactor_off_first_component D F G Q hF0 hG hQ hGQ hzero
      P.val P.property hH hPG
    apply hP
    simp only [clearedDifference, hidentity P hPQ, sub_self, mul_zero]
  refine ⟨?_, zero_on_factor_mem_component_or_intersection D F G hG P.val P.property hPG⟩
  rw [MinimumEquationComponents.eval_mapped_cofactor, hPG, map_zero]

theorem clearedDifference_on_first_component (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (m u : D → L) (qi qj : MvPolynomial (Fin 3) L)
    (hidentity : ∀ P : D, P.val ∈ componentPoints D F G →
      m P = eval (representatives f D P) qi * u P) :
    ∀ P : D, P.val ∈ componentPoints D F G →
      clearedDifference f D F G Q m u qj P = f (eval P.val.rep (pairCofactor F G Q)) *
        eval (representatives f D P) (qi - qj) * u P := by
  intro P hP
  rw [clearedDifference, hidentity P hP, map_sub]
  ring

theorem clearedDifference_ne_zero_on_first_component_iff (f : K →+* L)
    (D : Finset (PlanePoint K)) (F G Q : MvPolynomial (Fin 3) K)
    (m u : D → L) (hu : ∀ P, u P ≠ 0) (qi qj : MvPolynomial (Fin 3) L)
    (hidentity : ∀ P : D, P.val ∈ componentPoints D F G →
      m P = eval (representatives f D P) qi * u P) :
    ∀ P : D, P.val ∈ componentPoints D F G →
      (clearedDifference f D F G Q m u qj P ≠ 0 ↔ eval (representatives f D P) (qi - qj) ≠ 0) := by
  intro P hP
  rw [clearedDifference_on_first_component f D F G Q m u qi qj hidentity P hP]
  have hH : f (eval P.val.rep (pairCofactor F G Q)) ≠ 0 := by
    exact fun hz => (pairCofactor_nonzero_on_component D F G Q P.val hP)
      ((map_eq_zero_iff f f.injective).mp hz)
  simp only [mul_ne_zero_iff]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨hH, h⟩, hu P⟩⟩

theorem clearedDifference_support_card_upper (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (m u : D → L) (q : MvPolynomial (Fin 3) L)
    (hidentity : ∀ P : D, P.val ∈ componentPoints D F Q →
      m P = eval (representatives f D P) q * u P) :
    (GlobalMomentSupport.supportIndices (clearedDifference f D F G Q m u q)).card ≤
      (componentPoints D F G).card + (intersectionPoints D F).card := by
  let W := GlobalMomentSupport.supportIndices (clearedDifference f D F G Q m u q)
  have hsub : W.image (fun P : D => P.val) ⊆ componentPoints D F G ∪ intersectionPoints D F := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    exact (clearedDifference_support_on_first_factor f D F G Q hF0 hG hQ hGQ hzero
      m u q hidentity i (Finset.mem_filter.mp hi).2).2
  have hcard := Finset.card_image_of_injective W (Subtype.val_injective :
    Function.Injective (fun P : D => P.val))
  calc
    _ = (W.image (fun P : D => P.val)).card := hcard.symm
    _ ≤ (componentPoints D F G ∪ intersectionPoints D F).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

def componentIndices (D : Finset (PlanePoint K)) (F G : MvPolynomial (Fin 3) K) : Finset D :=
  (componentPoints D F G).subtype (fun P => P ∈ D)

theorem componentIndices_card (D : Finset (PlanePoint K)) (F G : MvPolynomial (Fin 3) K) :
    (componentIndices D F G).card = (componentPoints D F G).card := by
  unfold componentIndices
  rw [Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  exact Cylinder.DirectionCurveComponentCounting.componentPoints_subset D F G

section Counts

variable [Infinite L]

theorem clearedDifference_support_card_lower (f : K →+* L) (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (e a : ℕ)
    (hGhom : G.IsHomogeneous e) (hirr : Irreducible (MvPolynomial.map f G))
    (m u : D → L) (hu : ∀ P, u P ≠ 0) (qi qj : MvPolynomial (Fin 3) L)
    (hqi : qi.IsHomogeneous a) (hqj : qj.IsHomogeneous a) (hne : qi ≠ qj) (hae : a < e)
    (hidentity : ∀ P : D, P.val ∈ componentPoints D F G →
      m P = eval (representatives f D P) qi * u P) :
    (componentPoints D F G).card ≤
      (GlobalMomentSupport.supportIndices (clearedDifference f D F G Q m u qj)).card + e * a := by
  let T := componentIndices D F G
  let v : T → Fin 3 → L := fun i => representatives f D i.val
  have hv : ∀ i, v i ≠ 0 := fun i => representatives_nonzero f D i.val
  have hsep : Cylinder.HilbertEvaluation.ProjectivelyDistinct v := by
    intro i j hij c
    exact representatives_distinct f D i.val j.val (fun h => hij (Subtype.ext h)) c
  have hGzero : ∀ i, eval (v i) (MvPolynomial.map f G) = 0 := by
    intro i
    have hi : i.val.val ∈ componentPoints D F G := Finset.mem_subtype.mp i.property
    rw [MinimumEquationComponents.eval_mapped_cofactor, (Finset.mem_filter.mp hi).2.1, map_zero]
  let Z : Finset T := Finset.univ.filter (fun i => eval (v i) (qi - qj) = 0)
  let NZ : Finset T := Finset.univ.filter (fun i => eval (v i) (qi - qj) ≠ 0)
  have hZ : Z.card ≤ e * a := LocalCurveInterpolation.zeros_in_subset_card_le
    (MvPolynomial.map f G) (qi - qj) e a (hGhom.map f) hirr (hqi.sub hqj)
    (sub_ne_zero.mpr hne) hae v hv hsep hGzero Finset.univ
  have hsplit : Z.card + NZ.card = Fintype.card T := by
    simpa only [Z, NZ, ne_eq, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset T))
        (fun i => eval (v i) (qi - qj) = 0)
  have hNZsub : NZ.image (fun i : T => i.val) ⊆
      GlobalMomentSupport.supportIndices (clearedDifference f D F G Q m u qj) := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    have hcomponent : i.val.val ∈ componentPoints D F G := Finset.mem_subtype.mp i.property
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (clearedDifference_ne_zero_on_first_component_iff f D F G Q m u hu qi qj hidentity
        i.val hcomponent).mpr (Finset.mem_filter.mp hi).2⟩
  have hNZ := Finset.card_le_card hNZsub
  rw [Finset.card_image_of_injective NZ (Subtype.val_injective : Function.Injective
    (fun i : T => i.val))] at hNZ
  have hTcard : Fintype.card T = (componentPoints D F G).card := by
    simpa only [Fintype.card_coe] using componentIndices_card D F G
  omega

end Counts

end Cylinder.GlobalMomentCofactors

end
