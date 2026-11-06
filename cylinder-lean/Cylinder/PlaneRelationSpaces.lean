module

public import Cylinder.FiniteEvaluationDuality
public import Cylinder.HilbertCharacterFormulas
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Genuine homogeneous coefficient relation spaces and their rank defects. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneRelationSpaces

open Module Cylinder.HilbertEvaluation Cylinder.FiniteEvaluationDuality

variable {K I : Type*} [Field K] [Fintype I]

def relationSpace (v : I → Fin 3 → K) (d : ℕ) : Submodule K (I → K) :=
  (evaluationSpace v d).dualAnnihilator.comap coefficientDualMap

theorem mem_relationSpace (v : I → Fin 3 → K) (d : ℕ) (c : I → K) :
    c ∈ relationSpace v d ↔ PowerEvaluationRelation.Relation v c d := by
  change coefficientDualMap c ∈ (evaluationSpace v d).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h F hF
    exact h _ ⟨⟨F, hF⟩, rfl⟩
  · intro h w hw
    obtain ⟨F, rfl⟩ := hw
    exact h F.val F.property

def relationSpaceEquivAnnihilator (v : I → Fin 3 → K) (d : ℕ) :
    relationSpace v d ≃ₗ[K] (evaluationSpace v d).dualAnnihilator :=
  LinearEquiv.ofBijective (coefficientDualMap.submoduleComap (evaluationSpace v d).dualAnnihilator)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact coefficientDualMap_injective (congrArg Subtype.val hab),
      LinearMap.submoduleComap_surjective_of_surjective _ _ coefficientDualMap_surjective⟩

theorem relationSpace_finrank (v : I → Fin 3 → K) (d : ℕ) :
    finrank K (relationSpace v d) = Fintype.card I - hilbert v d := by
  have heq := (relationSpaceEquivAnnihilator v d).finrank_eq
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq (evaluationSpace v d)
  change hilbert v d + finrank K (evaluationSpace v d).dualAnnihilator = finrank K (I → K) at hdim
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  omega

theorem relationSpace_character_formula [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s : ℕ) (hs : Cylinder.PlaneBinaryReduction.InitialDegree v s) (d : ℕ) :
    finrank K (relationSpace v d) = ∑ i ∈ Finset.range s,
      ((Cylinder.HilbertCharacterFormulas.numericalCharacter v i - (d + 1)) - (i - (d + 1))) := by
  rw [relationSpace_finrank]
  exact Cylinder.HilbertCharacterFormulas.defect_formula v hv hsep s
    (Cylinder.PlaneBinaryReduction.derivationShape v hv hsep s hs) d

end Cylinder.PlaneRelationSpaces

end
