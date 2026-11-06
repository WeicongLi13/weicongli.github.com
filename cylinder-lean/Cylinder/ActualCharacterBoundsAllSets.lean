module

public import Cylinder.ActualCharacterBounds
public import Cylinder.PlanePointModel

/-! The character bounds for every finite reduced point set, including the
empty set. On an empty set the true initial degree is zero, so every sum
and every truncated lower bound in the manuscript is zero. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ActualCharacterBoundsAllSets

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas

variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
theorem initialDegree_eq_zero_of_empty [IsEmpty I]
    (v : I → Fin 3 → K) (s : ℕ) (hs : InitialDegree v s) : s = 0 := by
  let oneForm : Forms K 0 := ⟨1, isHomogeneous_one (Fin 3) K⟩
  have hmem : oneForm ∈ idealPiece v 0 := by
    rw [idealPiece_eq_kernel]
    apply LinearMap.mem_ker.mpr
    funext i
    exact isEmptyElim i
  have hne : oneForm ≠ 0 := by
    intro hz
    have hval := congrArg Subtype.val hz
    exact one_ne_zero (show (1 : PlaneRing K) = 0 from hval)
  by_contra hs0
  rw [hs.2 0 (Nat.pos_of_ne_zero hs0), Submodule.mem_bot] at hmem
  exact hne hmem

variable [Infinite K]

/-- The full-support version of `prop:charbound` has no nonempty-set
premise. Its conclusions hold for every natural relation degree. -/
theorem full_support_character_bounds
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s : ℕ) (hs : InitialDegree v s) (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) :
    (∀ i < s, max s (d + 2 - i) ≤ numericalCharacter v i) ∧
      (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ≤ Fintype.card I ∧
      s * (d + 3 - s) ≤ (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ∧
      ∀ t, t ≤ s → t * (d + 3 - t) ≤ Fintype.card I := by
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    exact Cylinder.ActualCharacterBounds.full_support_character_bounds
      v hv hsep s hs c hc d hrel
  · let : IsEmpty I := not_nonempty_iff.mp hI
    have hs0 := initialDegree_eq_zero_of_empty v s hs
    subst s
    refine ⟨?_, by simp, by simp, ?_⟩
    · intro i hi
      omega
    · intro t ht
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      simp [ht0]

/-- The same bounds on a literal finite set of projective points; all
representative nonzero and distinct conditions are derived from the set. -/
theorem projective_full_support_character_bounds
    (D : Finset (PlanePointModel.Plane K)) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s)
    (c : D → K) (hc : ∀ P, c P ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation (PlanePointModel.representatives D) c d) :
    (∀ i < s, max s (d + 2 - i) ≤ numericalCharacter (PlanePointModel.representatives D) i) ∧
      (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ≤ D.card ∧
      s * (d + 3 - s) ≤ (∑ i ∈ Finset.range s, (max s (d + 2 - i) - i)) ∧
      ∀ t, t ≤ s → t * (d + 3 - t) ≤ D.card := by
  simpa only [Fintype.card_coe] using
    full_support_character_bounds (PlanePointModel.representatives D)
      (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D)
      s hs c hc d hrel

end Cylinder.ActualCharacterBoundsAllSets

end
