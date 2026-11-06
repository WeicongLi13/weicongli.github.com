module

public import Cylinder.GapRelations
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Genuine minimal evaluation dependence gives a full-support relation

Dependence means the actual homogeneous evaluation map is not surjective.
Minimality means that deleting any one actual point makes it surjective.
The relation is constructed from a nonzero annihilating linear functional.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.MinimalEvaluationRelation
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.GapRelations
variable {K I : Type*} [Field K] [Fintype I]

def Delete (i : I) := {k : I // k ≠ i}

instance delete_fintype (i : I) : Fintype (Delete i) := by
  unfold Delete
  infer_instance

def deleteRepresentatives (v : I → Fin 3 → K) (i : I) : Delete i → Fin 3 → K :=
  fun k => v k.val

def MinimallyDependent (v : I → Fin 3 → K) (d : ℕ) : Prop :=
  ¬Function.Surjective (evaluationMap v d) ∧
    ∀ i, Function.Surjective (evaluationMap (deleteRepresentatives v i) d)

theorem dependent_has_nonzero_relation (v : I → Fin 3 → K) (d : ℕ)
    (hdep : ¬Function.Surjective (evaluationMap v d)) :
    ∃ c : I → K, (∃ i, c i ≠ 0) ∧ Cylinder.PowerEvaluationRelation.Relation v c d := by
  have hlt : evaluationSpace v d < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    exact hdep (LinearMap.range_eq_top.mp ht)
  obtain ⟨φ, hφ0, hker⟩ := (evaluationSpace v d).exists_le_ker_of_lt_top hlt
  let c : I → K := fun i => φ (Pi.single i (1 : K))
  have hφ (w : I → K) : φ w = ∑ i, c i * w i := by
    calc
      φ w = φ (∑ i, (w i) • (Pi.single i (1 : K) : I → K)) :=
        congrArg φ (pi_eq_sum_univ' w)
      _ = ∑ i, c i * w i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        change w i * c i = c i * w i
        exact mul_comm _ _
  have hc : ∃ i, c i ≠ 0 := by
    by_contra! hz
    apply hφ0
    apply LinearMap.ext
    intro w
    simp only [hφ, hz, zero_mul, Finset.sum_const_zero, LinearMap.zero_apply]
  refine ⟨c, hc, ?_⟩
  intro F hF
  have hm : evaluationMap v d ⟨F, hF⟩ ∈ evaluationSpace v d := ⟨⟨F, hF⟩, rfl⟩
  have hzero := hker hm
  change φ (fun i => eval (v i) F) = 0 at hzero
  rwa [hφ] at hzero

theorem relation_on_delete_of_zero (v : I → Fin 3 → K) (c : I → K) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) (i : I) (hci : c i = 0) :
    Cylinder.PowerEvaluationRelation.Relation (deleteRepresentatives v i)
      (fun k => c k.val) d := by
  intro F hF
  have hfull := hrel F hF
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun k : I => k ≠ i)
    (fun k => c k * eval (v k) F)
  have hzero : (∑ k : {k : I // ¬k ≠ i}, c k.val * eval (v k.val) F) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val = i := not_not.mp k.property
    simp only [hk, hci, zero_mul]
  rw [hzero, add_zero, hfull] at hsplit
  exact hsplit

theorem minimally_dependent_has_full_support (v : I → Fin 3 → K) (d : ℕ)
    (hmin : MinimallyDependent v d) :
    ∃ c : I → K, (∀ i, c i ≠ 0) ∧ Cylinder.PowerEvaluationRelation.Relation v c d := by
  obtain ⟨c, ⟨k, hck⟩, hrel⟩ := dependent_has_nonzero_relation v d hmin.1
  refine ⟨c, ?_, hrel⟩
  intro i hci
  have hdel := relation_on_delete_of_zero v c d hrel i hci
  have hz := relation_zero_of_surjective (deleteRepresentatives v i) (fun k => c k.val) d
    (hmin.2 i) hdel
  by_cases hki : k = i
  · exact hck (hki ▸ hci)
  · exact hck (hz ⟨k, hki⟩)

theorem minimally_dependent_nonempty (v : I → Fin 3 → K) (d : ℕ)
    (hmin : MinimallyDependent v d) : Nonempty I := by
  obtain ⟨_, ⟨i, _⟩, _⟩ := dependent_has_nonzero_relation v d hmin.1
  exact ⟨i⟩

end Cylinder.MinimalEvaluationRelation
end
