module

public import Cylinder.PowerEvaluationRelation
public import Cylinder.PlaneBinaryReduction

/-! Actual degree-one plane forms and their unique coefficient vectors. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.PlaneLinearForms

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PowerEvaluationRelation

variable {K : Type*} [Field K]

def linearFormMap : (Fin 3 → K) →ₗ[K] Forms K 1 where
  toFun a := ⟨linearForm a, IsHomogeneous.sum Finset.univ _ 1
    (fun i _ => isHomogeneous_C_mul_X (a i) i)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [linearForm, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp [linearForm, smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem eval_single_linearForm (a : Fin 3 → K) (j : Fin 3) :
    eval (Pi.single j 1) (linearForm a) = a j := by
  simp [linearForm, Pi.single_apply]

theorem linearFormMap_injective : Function.Injective (linearFormMap (K := K)) := by
  intro a b h
  funext j
  have h' := congrArg (fun P : Forms K 1 => eval (Pi.single j 1) P.val) h
  change eval (Pi.single j 1) (linearForm a) = eval (Pi.single j 1) (linearForm b) at h'
  simpa only [eval_single_linearForm] using h'

theorem linearFormMap_surjective : Function.Surjective (linearFormMap (K := K)) := by
  have hdim : finrank K (Fin 3 → K) = finrank K (Forms K 1) := by
    rw [show 1 = 0 + 1 from rfl, Cylinder.PlaneBinaryReduction.forms_rank_succ,
      Cylinder.PlaneBinaryReduction.forms_finrank_zero]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp linearFormMap_injective

/-- Every true homogeneous plane form of degree one has actual linear coefficients. -/
theorem exists_coefficients (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 1) :
    ∃ a : Fin 3 → K, F = linearForm a := by
  obtain ⟨a, ha⟩ := linearFormMap_surjective ⟨F, hF⟩
  exact ⟨a, (congrArg Subtype.val ha).symm⟩

theorem coefficients_ne_zero (F : MvPolynomial (Fin 3) K) (a : Fin 3 → K)
    (hF0 : F ≠ 0) (hF : F = linearForm a) : a ≠ 0 := by
  intro ha
  apply hF0
  rw [hF, ha]
  simp [linearForm]

end Cylinder.PlaneLinearForms

end
