module

public import Cylinder.FinalAssociatedGraded
public import Cylinder.GenericPlaneLine
public import Cylinder.HomogeneousAffineChart
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The geometric hypotheses of Proposition 5.2 imply the leading-term
hypotheses for every chart whose line at infinity misses the intersection. -/

@[expose] public section
noncomputable section

namespace Cylinder.FinalAssociatedChart

open MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CurvePolarLocal Cylinder.HomogeneousAffineChart
open Cylinder.FinalAssociatedGraded
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem eval_binary_dehomogenize (P : BinaryRing K) (a : K) :
    (BinaryHomogenization.dehomogenize P).eval a = eval ![a, 1] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [BinaryHomogenization.dehomogenize]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.eval_mul, map_mul, hP]
    congr 1
    fin_cases i <;> simp [BinaryHomogenization.dehomogenize]

theorem binary_positive_has_projective_zero (P : BinaryRing K) (n : ℕ)
    (hn : 0 < n) (hP : P.IsHomogeneous n) :
    ∃ u : Fin 2 → K, u ≠ 0 ∧ eval u P = 0 := by
  by_cases hinf : eval ![1, 0] P = 0
  · exact ⟨![1, 0], by intro h; have := congrFun h 0; simpa using this, hinf⟩
  · have hdegree : (BinaryHomogenization.dehomogenize P).degree ≠ 0 := by
      intro hd
      have hC := Polynomial.eq_C_of_degree_le_zero (le_of_eq hd)
      have hrec := Polynomial.homogenize_eq_of_isHomogeneous hP
        (p := BinaryHomogenization.dehomogenize P) rfl
      rw [hC, Polynomial.homogenize_C] at hrec
      apply hinf
      rw [← hrec]
      simp [Nat.ne_of_gt hn]
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (BinaryHomogenization.dehomogenize P) hdegree
    refine ⟨![a, 1], ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simpa using this
    · rw [← eval_binary_dehomogenize]
      exact ha

theorem binary_coprime_of_no_common_projective_zero (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (havoid : ∀ u : Fin 2 → K, u ≠ 0 → eval u F ≠ 0 ∨ eval u G ≠ 0) :
    IsRelPrime F G := by
  have hc : IsCoprime (BinaryHomogenization.dehomogenize F) (BinaryHomogenization.dehomogenize G) := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr
    intro a
    have h := havoid ![a, 1] (by intro hz; have := congrFun hz 1; simpa using this)
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
      eval_binary_dehomogenize] using h
  have hinf := havoid ![1, 0] (by intro hz; have := congrFun hz 0; simpa using this)
  rcases hinf with h | h
  · exact GenericPlaneLine.binary_relPrime_of_dehomogenize_coprime F G e t hF hG h hc
  · exact (GenericPlaneLine.binary_relPrime_of_dehomogenize_coprime G F t e hG hF h hc.symm).symm

/-- The line `Z = 0` avoids the projective intersection. -/
def AvoidsInfinity (F G : HomogeneousPlanePolynomial (K := K)) : Prop :=
  ∀ u : Fin 2 → K, u ≠ 0 →
    eval (fun i : Option (Fin 2) => i.elim 0 u) F ≠ 0 ∨
      eval (fun i : Option (Fin 2) => i.elim 0 u) G ≠ 0

theorem leading_data_of_avoiding (F G : HomogeneousPlanePolynomial (K := K))
    (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (havoid : AvoidsInfinity F G) :
    LeadingData (chartAt 1 F) (chartAt 1 G) e t := by
  have hFhom := chartAt_zero_homogeneous e F hF
  have hGhom := chartAt_zero_homogeneous t G hG
  have hav : ∀ u : Fin 2 → K, u ≠ 0 → eval u (chartAt 0 F) ≠ 0 ∨ eval u (chartAt 0 G) ≠ 0 := by
    intro u hu
    simpa only [eval_chartAt] using havoid u hu
  have hFzero : chartAt 0 F ≠ 0 := by
    intro hz
    obtain ⟨u, hu, hGu⟩ := binary_positive_has_projective_zero (chartAt 0 G) t ht hGhom
    rcases hav u hu with h | h
    · exact h (by rw [hz, map_zero])
    · exact h hGu
  have hGzero : chartAt 0 G ≠ 0 := by
    intro hz
    obtain ⟨u, hu, hFu⟩ := binary_positive_has_projective_zero (chartAt 0 F) e he hFhom
    rcases hav u hu with h | h
    · exact h hFu
    · exact h (by rw [hz, map_zero])
  refine ⟨chartAt_one_totalDegree e F hF hFzero, chartAt_one_totalDegree t G hG hGzero, ?_, ?_⟩
  · rwa [top_component_chartAt e F hF]
  · rw [top_component_chartAt e F hF, top_component_chartAt t G hG]
    exact binary_coprime_of_no_common_projective_zero _ _ e t hFhom hGhom hav

/-- Proposition 5.2 in coordinates with the avoiding line equal to `Z = 0`.
No leading-term coprimality or graded-ring isomorphism is an extra hypothesis. -/
def associatedgraded (F G : HomogeneousPlanePolynomial (K := K))
    (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (havoid : AvoidsInfinity F G) :
    let d := leading_data_of_avoiding F G e t he ht hF hG havoid
    letI := ringStructure d
    Associated (chartAt 1 F) (chartAt 1 G) ≃+*
      QuotientRing (chartAt 0 F) (chartAt 0 G) := by
  dsimp only
  letI := ringStructure (leading_data_of_avoiding F G e t he ht hF hG havoid)
  exact (associatedRingEquiv (leading_data_of_avoiding F G e t he ht hF hG havoid)).trans
    (Ideal.quotEquivOfEq (by rw [top_component_chartAt e F hF, top_component_chartAt t G hG]))

theorem associatedgraded_homogeneous (F G : HomogeneousPlanePolynomial (K := K))
    (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (havoid : AvoidsInfinity F G)
    (n : ℕ) (P : BinaryForms K n) :
    associatedgraded F G e t he ht hF hG havoid
      (DirectSum.lof K ℕ (FinalAssociatedPieces.Piece (chartAt 1 F) (chartAt 1 G)) n
        (FinalAssociatedPieces.gradeMap (chartAt 1 F) (chartAt 1 G) n P)) =
      Ideal.Quotient.mk (equationsIdeal (chartAt 0 F) (chartAt 0 G)) P.val := by
  simp only [associatedgraded, id_eq, RingEquiv.trans_apply, associatedRingEquiv_apply,
    sumEquiv_homogeneous, Ideal.quotEquivOfEq_mk]

/-- The paper's ring isomorphism identifies every homogeneous degree, with
no restriction to positive degrees. -/
theorem associatedgraded_degree_range (F G : HomogeneousPlanePolynomial (K := K))
    (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (havoid : AvoidsInfinity F G)
    (n : ℕ) :
    Set.range (fun a : FinalAssociatedPieces.Piece (chartAt 1 F) (chartAt 1 G) n =>
      associatedgraded F G e t he ht hF hG havoid
        (DirectSum.lof K ℕ (FinalAssociatedPieces.Piece (chartAt 1 F) (chartAt 1 G)) n a)) =
      (BinaryCompleteIntersectionGraded.quotientPiece (chartAt 0 F) (chartAt 0 G) n : Set _) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨P, rfl⟩ := FinalAssociatedPieces.gradeMap_surjective (chartAt 1 F) (chartAt 1 G) n a
    exact ⟨P, (associatedgraded_homogeneous F G e t he ht hF hG havoid n P).symm⟩
  · rintro ⟨P, rfl⟩
    exact ⟨FinalAssociatedPieces.gradeMap (chartAt 1 F) (chartAt 1 G) n P,
      associatedgraded_homogeneous F G e t he ht hF hG havoid n P⟩

#print axioms associatedgraded
#print axioms associatedgraded_degree_range
#print axioms Cylinder.FinalAssociatedGraded.multiplication_filtered_classes

end Cylinder.FinalAssociatedChart

end
