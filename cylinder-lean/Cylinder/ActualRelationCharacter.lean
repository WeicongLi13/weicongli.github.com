module

public import Cylinder.GapRelations

/-! Actual full-support evaluation relations force numerical-character bounds.
The initial bound follows from the actual evaluation rank defect; every later
gap bound is supplied by the proved curve-and-complement gap theorem. -/

@[expose] public section
noncomputable section
namespace Cylinder.ActualRelationCharacter
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.HilbertCharacterFormulas Cylinder.PlaneGap Cylinder.GapRelations
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

theorem first_character_bound (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ) (hs : InitialDegree v s)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) :
    d + 2 ≤ numericalCharacter v 0 := by
  have hne : hilbert v d ≠ Fintype.card I := by
    intro hH
    have hz := relation_zero_of_surjective v c d
      (evaluationMap_surjective_of_hilbert_eq_card v d hH) hrel
    let i : I := Classical.choice inferInstance
    exact hc i (hz i)
  have hpos : 0 < Fintype.card I - hilbert v d := by
    have := hilbert_le_card v d
    omega
  have hn := (defect_positive_iff v hv hsep s (derivationShape v hv hsep s hs) d).mp hpos
  omega

theorem character_gap_bounds (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ) (hs : InitialDegree v s)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) :
    (d + 2 ≤ numericalCharacter v 0) ∧
      ∀ j, 0 < j → j < s →
        numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1) →
          d + 2 ≤ numericalCharacter v j :=
  ⟨first_character_bound v hv hsep s hs c hc d hrel,
    fun j hj0 hjs hgap => full_support_gap_bound v hv hsep s j hs hj0 hjs hgap c hc d hrel⟩

end Cylinder.ActualRelationCharacter
end
