module

public import Cylinder.PlaneBinaryReduction

/-! Every actual finite plane evaluation system has a genuine first nonzero
homogeneous vanishing piece. The witness is obtained from actual rank-nullity. -/

@[expose] public section
noncomputable section
namespace Cylinder.InitialDegreeExists
open Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
theorem independent_iff_surjective (v : I → Fin 3 → K) (d : ℕ) :
    Cylinder.EvaluationProjection.Independent v d ↔ Function.Surjective (evaluationMap v d) := by
  constructor
  · intro h w
    obtain ⟨P, hP, hvals⟩ := h w
    exact ⟨⟨P, hP⟩, funext hvals⟩
  · intro h w
    obtain ⟨P, hP⟩ := h w
    exact ⟨P.val, P.property, fun i => congrFun hP i⟩

theorem forms_finrank_lower (d : ℕ) : d + 1 ≤ finrank K (Forms K d) := by
  induction d with
  | zero => rw [forms_finrank_zero]
  | succ d ih => rw [forms_rank_succ]; omega

theorem exists_initialDegree (v : I → Fin 3 → K) : ∃ s, InitialDegree v s := by
  have hnonzero : ∃ d, idealPiece v d ≠ ⊥ := by
    refine ⟨Fintype.card I, ?_⟩
    have hdim := ideal_piece_dimension v (Fintype.card I)
    rw [← idealPiece_eq_kernel] at hdim
    have hlower := forms_finrank_lower (K := K) (Fintype.card I)
    have hupper := hilbert_le_card v (Fintype.card I)
    intro hz
    rw [hz, finrank_bot] at hdim
    omega
  refine ⟨Nat.find hnonzero, Nat.find_spec hnonzero, ?_⟩
  intro d hd
  exact not_not.mp (Nat.find_min hnonzero hd)

end Cylinder.InitialDegreeExists
end
