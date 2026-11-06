module

public import Cylinder.LocalCurveTheorem

/-! Reindexing finite point families preserves the actual evaluation geometry
and its numerical character. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalPointReindexing
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

def functionReindex (e : I ≃ J) : (I → K) ≃ₗ[K] (J → K) where
  toFun c j := c (e.symm j)
  invFun c i := c (e i)
  left_inv c := by funext i; simp
  right_inv c := by funext j; simp
  map_add' c d := rfl
  map_smul' a c := rfl

theorem hilbert_reindex (e : I ≃ J) (v : I → Fin 3 → K) (d : ℕ) :
    hilbert (fun j => v (e.symm j)) d = hilbert v d := by
  have hmap : evaluationMap (fun j => v (e.symm j)) d =
      (functionReindex (K := K) e).toLinearMap.comp (evaluationMap v d) := rfl
  have hr : evaluationSpace (fun j => v (e.symm j)) d =
      (evaluationSpace v d).map (functionReindex (K := K) e).toLinearMap := by
    change LinearMap.range _ = (LinearMap.range _).map _
    rw [hmap, LinearMap.range_comp]
  change finrank K (evaluationSpace (fun j => v (e.symm j)) d) = _
  rw [hr]
  exact LinearEquiv.finrank_map_eq (functionReindex (K := K) e) (evaluationSpace v d)

theorem idealPiece_reindex (e : I ≃ J) (v : I → Fin 3 → K) (d : ℕ) :
    idealPiece (fun j => v (e.symm j)) d = idealPiece v d := by
  ext Q
  change Q.val ∈ (vanishingIdeal (fun j => v (e.symm j))).toIdeal ↔
    Q.val ∈ (vanishingIdeal v).toIdeal
  rw [homogeneous_mem_vanishingIdeal _ Q.val d Q.property,
    homogeneous_mem_vanishingIdeal _ Q.val d Q.property]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (e i)
  · intro h j
    exact h (e.symm j)

theorem initialDegree_reindex (e : I ≃ J) (v : I → Fin 3 → K) (s : ℕ) :
    InitialDegree (fun j => v (e.symm j)) s ↔ InitialDegree v s := by
  simp only [InitialDegree, idealPiece_reindex e v]

theorem numericalCharacter_reindex [Infinite K] (e : I ≃ J) (v : I → Fin 3 → K) :
    numericalCharacter (fun j => v (e.symm j)) = numericalCharacter v := by
  have hH : hilbert (fun j => v (e.symm j)) = hilbert v := funext (hilbert_reindex e v)
  funext i
  change NumericCharacterSequence.character (NumericCharacterSequence.firstDifference
    (hilbert (fun j => v (e.symm j)))) (Fintype.card J) i = _
  rw [hH, ← Fintype.card_congr e]
  rfl

theorem relation_reindex (e : I ≃ J) (v : I → Fin 3 → K) (c : I → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    PowerEvaluationRelation.Relation (fun j => v (e.symm j)) (fun j => c (e.symm j)) d := by
  intro Q hQ
  rw [← Fintype.sum_equiv e]
  · exact hrel Q hQ
  · intro i
    simp only [Equiv.symm_apply_apply]

#print axioms hilbert_reindex
#print axioms idealPiece_reindex
#print axioms initialDegree_reindex
#print axioms numericalCharacter_reindex
#print axioms relation_reindex

end Cylinder.LocalPointReindexing
end
