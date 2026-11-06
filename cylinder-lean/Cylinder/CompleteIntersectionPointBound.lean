module

public import Cylinder.CompleteIntersectionHilbert
public import Cylinder.JetIdeal
public import Cylinder.PlanePointModel

/-! The degree-product bound for actual finite reduced intersection point sets. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CompleteIntersectionPointBound

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem cardinal_bound (F G : MvPolynomial (Fin 3) K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hpoints : ∀ i, eval (v i) F = 0 ∧ eval (v i) G = 0) :
    Fintype.card I ≤ e * t := by
  let J : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {F, G}
  let d := max (Fintype.card I - 1) (e + t - 2)
  have hJ : J ≤ representativeIdeal v := by
    apply Ideal.span_le.mpr
    intro H hH
    rcases Set.mem_insert_iff.mp hH with hHF | hH
    · subst H
      exact (mem_representativeIdeal v F).mpr (fun i => (hpoints i).1)
    · rw [Set.mem_singleton_iff] at hH
      subst H
      exact (mem_representativeIdeal v G).mpr (fun i => (hpoints i).2)
  have hker : JetIdeal.idealPiece J d ≤ LinearMap.ker (HilbertEvaluation.evaluationMap v d) := by
    intro P hP
    have hval : ∀ i, eval (v i) P.val = 0 := (mem_representativeIdeal v P.val).mp (hJ hP)
    exact LinearMap.mem_ker.mpr (funext hval)
  let f := (JetIdeal.idealPiece J d).liftQ (HilbertEvaluation.evaluationMap v d) hker
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨P, hP, hvals⟩ := EvaluationProjection.independent_of_le v hv
      (Fintype.card I - 1) d (le_max_left _ _) (independent_card_sub_one v hv hsep) y
    exact ⟨Submodule.Quotient.mk ⟨P, hP⟩, funext hvals⟩
  have hlower := LinearMap.finrank_le_finrank_of_surjective hsurj
  have hdim : finrank K (Forms K d ⧸ JetIdeal.idealPiece J d) = e * t :=
    Cylinder.CompleteIntersectionHilbert.forms_quotient_finrank F G e t d he ht hF hG
      hF0 hcop (le_max_right _ _)
  simpa only [Module.finrank_fintype_fun_eq_card, hdim] using hlower

/-- This point bound uses the actual finite projective set and its distinct
nonzero representatives; no intersection cardinality estimate is assumed. -/
theorem projective_cardinal_bound (F G : MvPolynomial (Fin 3) K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (T : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ x : T, eval x.val.rep F = 0 ∧ eval x.val.rep G = 0) :
    T.card ≤ e * t := by
  simpa only [Fintype.card_coe] using cardinal_bound F G e t he ht hF hG hF0 hcop
    (PlanePointModel.representatives T) (PlanePointModel.representatives_nonzero T)
    (PlanePointModel.representatives_distinct T) hpoints

end Cylinder.CompleteIntersectionPointBound

end
