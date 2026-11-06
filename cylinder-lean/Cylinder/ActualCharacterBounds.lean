module

public import Cylinder.ActualRelationCharacter
public import Cylinder.MinimalEvaluationRelation
public import Cylinder.CharacterBounds

/-!
# Character bounds for actual plane evaluation relations

Both the full-support and the minimally dependent versions use actual
homogeneous evaluation maps. Numerical-character shape and every gap bound
are derived from the actual point ideal and the actual relation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Cylinder.ActualCharacterBounds
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.HilbertCharacterFormulas Cylinder.ActualRelationCharacter
open Cylinder.NumericCharacterSequence Cylinder.MinimalEvaluationRelation
variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem full_support_character_bounds [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s : ℕ) (hs : InitialDegree v s) (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) :
    (∀ i < s, max s (d + 2 - i) ≤ numericalCharacter v i) ∧
      (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ≤ Fintype.card I ∧
      s * (d + 3 - s) ≤ (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ∧
      ∀ t, t ≤ s → t * (d + 3 - t) ≤ Fintype.card I := by
  have hshape := derivationShape v hv hsep s hs
  obtain ⟨h0, hgap⟩ := character_gap_bounds v hv hsep s hs c hc d hrel
  have hlength := HilbertCharacterFormulas.length_formula v hv hsep s hshape
  refine ⟨fun i hi => Cylinder.CharacterBounds.character_lower hshape h0 hgap i hi, ?_,
    Cylinder.CharacterBounds.max_sum_bound s d, ?_⟩
  · rw [hlength]
    exact Cylinder.CharacterBounds.character_sum_bound hshape h0 hgap
  · intro t ht
    rw [hlength]
    exact Cylinder.CharacterBounds.truncated_character_bound hshape h0 hgap t ht

theorem minimally_dependent_character_bounds
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s : ℕ) (hs : InitialDegree v s) (d : ℕ) (hmin : MinimallyDependent v d) :
    (∀ i < s, max s (d + 2 - i) ≤ numericalCharacter v i) ∧
      (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ≤ Fintype.card I ∧
      s * (d + 3 - s) ≤ (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ∧
      ∀ t, t ≤ s → t * (d + 3 - t) ≤ Fintype.card I := by
  let : Nonempty I := minimally_dependent_nonempty v d hmin
  obtain ⟨c, hc, hrel⟩ := minimally_dependent_has_full_support v d hmin
  exact full_support_character_bounds v hv hsep s hs c hc d hrel

end Cylinder.ActualCharacterBounds
end
