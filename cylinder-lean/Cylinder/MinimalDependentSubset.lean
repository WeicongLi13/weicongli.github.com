module

public import Cylinder.MinimalEvaluationRelation

/-! A genuine minimally dependent subset of a finite evaluation system. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.MinimalDependentSubset

open Cylinder.HilbertEvaluation Cylinder.MinimalEvaluationRelation

variable {K A : Type*} [Field K]

def eraseEquiv (W : Finset A) (i : W) : Delete i ≃ W.erase i.val :=
  Equiv.ofBijective (fun k => ⟨k.val.val, Finset.mem_erase.mpr
    ⟨fun h => k.property (Subtype.ext h), k.val.property⟩⟩) (by
      constructor
      · intro k l h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : W.erase i.val => x.val) h
      · intro x
        let k : W := ⟨x.val, (Finset.mem_erase.mp x.property).2⟩
        have hki : k ≠ i := fun h => (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)
        exact ⟨⟨k, hki⟩, Subtype.ext rfl⟩)

/-- Dependence is tested on the actual evaluation map. Minimality is obtained
by minimizing the cardinality of actual dependent subsets. -/
theorem exists_minimally_dependent_subset (v : A → Fin 3 → K) (D : Finset A) (d : ℕ)
    (hdep : ¬Function.Surjective (evaluationMap (fun x : D => v x.val) d)) :
    ∃ W : Finset A, W ⊆ D ∧ MinimallyDependent (fun x : W => v x.val) d := by
  have hex : ∃ n : ℕ, ∃ W : Finset A, W ⊆ D ∧
      ¬Function.Surjective (evaluationMap (fun x : W => v x.val) d) ∧ W.card = n :=
    ⟨D.card, D, Finset.Subset.refl D, hdep, rfl⟩
  obtain ⟨W, hWD, hWdep, hWcard⟩ := Nat.find_spec hex
  refine ⟨W, hWD, hWdep, ?_⟩
  intro i
  have hsurj : Function.Surjective (evaluationMap (fun x : W.erase i.val => v x.val) d) := by
    by_contra hbad
    have hsmall : (W.erase i.val).card < Nat.find hex := by
      rw [Finset.card_erase_of_mem i.property, hWcard]
      have hnpos : 0 < Nat.find hex := by
        have hpos := Finset.card_pos.mpr ⟨i.val, i.property⟩
        rwa [hWcard] at hpos
      omega
    exact Nat.find_min hex hsmall ⟨W.erase i.val, (Finset.erase_subset _ _).trans hWD, hbad, rfl⟩
  let e := eraseEquiv W i
  intro y
  obtain ⟨P, hP⟩ := hsurj (fun x => y (e.symm x))
  refine ⟨P, ?_⟩
  funext k
  have h := congrFun hP (e k)
  change (P.val.eval (v k.val.val)) = y (e.symm (e k)) at h
  change (P.val.eval (v k.val.val)) = y k
  simpa only [Equiv.symm_apply_apply] using h

end Cylinder.MinimalDependentSubset

end
