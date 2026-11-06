module

public import Cylinder.PlaneRelationSpaces
public import Cylinder.PlaneBinaryReduction

/-! Multiplication by an actual full-support relation embeds low-degree forms. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.WeightedFormRelations

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.PlaneRelationSpaces

variable {K I : Type*} [Field K] [Fintype I]

def weightedFormMap (v : I → Fin 3 → K) (c : I → K) (hc : ∀ i, c i ≠ 0)
    (d q : ℕ) (hqd : q ≤ d) (hrel : PowerEvaluationRelation.Relation v c d) :
    Forms K q →ₗ[K] relationSpace v (d - q) :=
  LinearMap.codRestrict (relationSpace v (d - q))
    ((diagonalEquiv c hc).toLinearMap.comp (evaluationMap v q)) (fun F => by
      apply (mem_relationSpace v (d - q) _).mpr
      intro G hG
      have hhom : (F.val * G).IsHomogeneous d := by
        have h := F.property.mul hG
        rw [show q + (d - q) = d by omega] at h
        exact h
      have h := hrel (F.val * G) hhom
      change (∑ i, (c i * eval (v i) F.val) * eval (v i) G) = 0
      simpa only [map_mul, mul_assoc] using h)

theorem weightedFormMap_apply (v : I → Fin 3 → K) (c : I → K) (hc : ∀ i, c i ≠ 0)
    (d q : ℕ) (hqd : q ≤ d) (hrel : PowerEvaluationRelation.Relation v c d)
    (F : Forms K q) (i : I) :
    (weightedFormMap v c hc d q hqd hrel F).val i = c i * eval (v i) F.val := rfl

theorem evaluationMap_injective_of_lt_initial (v : I → Fin 3 → K) (e q : ℕ)
    (hs : InitialDegree v e) (hqe : q < e) : Function.Injective (evaluationMap v q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← idealPiece_eq_kernel, hs.2 q hqe]

theorem weightedFormMap_injective (v : I → Fin 3 → K) (c : I → K) (hc : ∀ i, c i ≠ 0)
    (e d q : ℕ) (hs : InitialDegree v e) (hqe : q < e) (hqd : q ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    Function.Injective (weightedFormMap v c hc d q hqd hrel) := by
  intro F G hFG
  apply evaluationMap_injective_of_lt_initial v e q hs hqe
  apply (diagonalEquiv c hc).injective
  exact congrArg Subtype.val hFG

theorem weightedFormMap_surjective_of_finrank (v : I → Fin 3 → K)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (e d q : ℕ)
    (hs : InitialDegree v e) (hqe : q < e) (hqd : q ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d)
    (hdim : finrank K (Forms K q) = finrank K (relationSpace v (d - q))) :
    Function.Surjective (weightedFormMap v c hc d q hqd hrel) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (weightedFormMap_injective v c hc e d q hs hqe hqd hrel)

theorem exists_weighted_form (v : I → Fin 3 → K)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (e d q : ℕ)
    (hs : InitialDegree v e) (hqe : q < e) (hqd : q ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d)
    (hdim : finrank K (Forms K q) = finrank K (relationSpace v (d - q)))
    (m : I → K) (hm : PowerEvaluationRelation.Relation v m (d - q)) :
    ∃ F : PlaneRing K, F.IsHomogeneous q ∧ ∀ i, m i = eval (v i) F * c i := by
  obtain ⟨F, hF⟩ := weightedFormMap_surjective_of_finrank v c hc e d q hs hqe hqd hrel hdim
    ⟨m, (mem_relationSpace v _ m).mpr hm⟩
  refine ⟨F.val, F.property, ?_⟩
  intro i
  have h := congrArg (fun x : relationSpace v (d - q) => x.val i) hF
  simpa only [weightedFormMap_apply, mul_comm] using h.symm

end Cylinder.WeightedFormRelations

end
