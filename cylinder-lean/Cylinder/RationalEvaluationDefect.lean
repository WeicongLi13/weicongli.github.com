module

public import Cylinder.RationalPolynomialEvaluation
public import Cylinder.IntegerEvaluationDuality
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The cokernel of the actual polynomial evaluation has the same
dimension as the manuscript's original coefficient relation space. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalEvaluationDefect

open MvPolynomial Module
open Cylinder.PlaneLaurentHomogeneous Cylinder.RationalPolynomialEvaluation
open Cylinder.FiniteEvaluationDuality

universe u
variable (K : Type u) [Field K] {I : Type u} [Fintype I]

def evaluationSpace (v : ℤ) (x : I → Fin 2 → K) : Submodule K (I → K) :=
  (polynomialEvaluation K v x).range

def hilbert (v : ℤ) (x : I → Fin 2 → K) : ℕ :=
  finrank K (evaluationSpace K v x)

def relations (v : ℤ) (x : I → Fin 2 → K) : Submodule K (I → K) :=
  (evaluationSpace K v x).dualAnnihilator.comap coefficientDualMap

theorem mem_relations (v : ℤ) (x : I → Fin 2 → K) (c : I → K) :
    c ∈ relations K v x ↔ ∀ H : integerForms K v,
      ∑ i, c i * eval (RationalFractionEvaluation.normalized K (x i)) H.val = 0 := by
  change coefficientDualMap c ∈ (evaluationSpace K v x).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h H
    exact h _ ⟨H, rfl⟩
  · intro h w hw
    obtain ⟨H, rfl⟩ := hw
    exact h H

theorem relations_eq_original (v : ℤ) (x : I → Fin 2 → K) :
    relations K v x = IntegerEvaluationDuality.integerCoefficientRelations x v := by
  ext c
  rw [mem_relations, IntegerEvaluationDuality.mem_integerCoefficientRelations]
  constructor
  · intro h H hH
    exact h ⟨H, hH⟩
  · intro h H
    exact h H.val H.property

def relationsEquivAnnihilator (v : ℤ) (x : I → Fin 2 → K) :
    relations K v x ≃ₗ[K] (evaluationSpace K v x).dualAnnihilator :=
  LinearEquiv.ofBijective
    (coefficientDualMap.submoduleComap (evaluationSpace K v x).dualAnnihilator)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact coefficientDualMap_injective (congrArg Subtype.val hab),
      LinearMap.submoduleComap_surjective_of_surjective _ _ coefficientDualMap_surjective⟩

theorem relations_finrank (v : ℤ) (x : I → Fin 2 → K) :
    finrank K (relations K v x) = Fintype.card I - hilbert K v x := by
  have he := (relationsEquivAnnihilator K v x).finrank_eq
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (evaluationSpace K v x)
  rw [Module.finrank_fintype_fun_eq_card] at hd
  change hilbert K v x + finrank K (evaluationSpace K v x).dualAnnihilator = _ at hd
  omega

theorem cokernel_finrank (v : ℤ) (x : I → Fin 2 → K) :
    finrank K ((I → K) ⧸ evaluationSpace K v x) = Fintype.card I - hilbert K v x := by
  have hd := (evaluationSpace K v x).finrank_quotient_add_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hd
  change finrank K ((I → K) ⧸ evaluationSpace K v x) + hilbert K v x = _ at hd
  omega

theorem cokernel_finrank_eq_original_relations (v : ℤ) (x : I → Fin 2 → K) :
    finrank K ((I → K) ⧸ evaluationSpace K v x) =
      finrank K (IntegerEvaluationDuality.integerCoefficientRelations x v) := by
  rw [← relations_eq_original K v x, relations_finrank, cokernel_finrank]

end Cylinder.RationalEvaluationDefect
end
