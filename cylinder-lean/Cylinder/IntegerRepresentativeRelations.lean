module

public import Cylinder.PlaneRelationSpaces
public import Cylinder.LinearEvaluationTransport
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Changing actual point representatives, with coherent coefficients in all integer degrees. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.IntegerRepresentativeRelations

open MvPolynomial Cylinder.PlaneRelationSpaces

variable {K I : Type*} [Field K] [Fintype I]

def integerRelations (v : I → Fin 3 → K) (j : ℤ) : Submodule K (I → K) :=
  if 0 ≤ j then relationSpace v j.toNat else ⊤

def coefficientScale (u : I → K) (hu : ∀ i, u i ≠ 0) (j : ℤ) : (I → K) ≃ₗ[K] (I → K) where
  toFun c i := u i ^ (-j) * c i
  invFun c i := u i ^ j * c i
  left_inv c := by
    funext i
    change u i ^ j * (u i ^ (-j) * c i) = c i
    rw [← mul_assoc, mul_comm (u i ^ j), zpow_neg_mul_zpow_self j (hu i), one_mul]
  right_inv c := by
    funext i
    change u i ^ (-j) * (u i ^ j * c i) = c i
    rw [← mul_assoc, zpow_neg_mul_zpow_self j (hu i), one_mul]
  map_add' c d := by funext i; exact mul_add _ _ _
  map_smul' a c := by
    funext i
    change u i ^ (-j) * (a * c i) = a * (u i ^ (-j) * c i)
    ring

theorem scaled_evaluation_sum (v : I → Fin 3 → K) (u c : I → K)
    (hu : ∀ i, u i ≠ 0) (j : ℤ) (hj : 0 ≤ j)
    (H : Cylinder.HilbertEvaluation.PlaneRing K) (hH : H.IsHomogeneous j.toNat) :
    (∑ i, coefficientScale u hu j c i * eval (u i • v i) H) =
      ∑ i, c i * eval (v i) H := by
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearEvaluationTransport.homogeneous_eval_smul H j.toNat hH]
  have hpow : u i ^ j = u i ^ j.toNat := by
    calc
      u i ^ j = u i ^ (j.toNat : ℤ) := congrArg (fun n : ℤ => u i ^ n) (Int.toNat_of_nonneg hj).symm
      _ = _ := zpow_natCast _ _
  have hcancel := zpow_neg_mul_zpow_self j (hu i)
  rw [hpow] at hcancel
  change (u i ^ (-j) * c i) * (u i ^ j.toNat * eval (v i) H) = _
  calc
    _ = (u i ^ (-j) * u i ^ j.toNat) * (c i * eval (v i) H) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem coefficientScale_mem_iff (v : I → Fin 3 → K) (u : I → K)
    (hu : ∀ i, u i ≠ 0) (j : ℤ) (c : I → K) :
    coefficientScale u hu j c ∈ integerRelations (fun i => u i • v i) j ↔
      c ∈ integerRelations v j := by
  by_cases hj : 0 ≤ j
  · simp only [integerRelations, if_pos hj, mem_relationSpace]
    constructor
    · intro h H hH
      rw [← scaled_evaluation_sum v u c hu j hj H hH]
      exact h H hH
    · intro h H hH
      rw [scaled_evaluation_sum v u c hu j hj H hH]
      exact h H hH
  · simp only [integerRelations, if_neg hj, Submodule.mem_top]

def representativeRelationsEquiv (v : I → Fin 3 → K) (u : I → K)
    (hu : ∀ i, u i ≠ 0) (j : ℤ) :
    integerRelations v j ≃ₗ[K] integerRelations (fun i => u i • v i) j where
  toFun c := ⟨coefficientScale u hu j c.val, (coefficientScale_mem_iff v u hu j c.val).mpr c.property⟩
  invFun c := ⟨(coefficientScale u hu j).symm c.val, by
    apply (coefficientScale_mem_iff v u hu j _).mp
    simpa only [LinearEquiv.apply_symm_apply] using c.property⟩
  left_inv c := by apply Subtype.ext; exact (coefficientScale u hu j).symm_apply_apply c.val
  right_inv c := by apply Subtype.ext; exact (coefficientScale u hu j).apply_symm_apply c.val
  map_add' c d := by apply Subtype.ext; exact (coefficientScale u hu j).map_add c.val d.val
  map_smul' a c := by apply Subtype.ext; exact (coefficientScale u hu j).map_smul a c.val

theorem rescaling_multiplication (v : I → Fin 3 → K) (u : I → K)
    (hu : ∀ i, u i ≠ 0) (j : ℤ) (a : ℕ)
    (Q : Cylinder.HilbertEvaluation.PlaneRing K) (hQ : Q.IsHomogeneous a) (c : I → K) :
    coefficientScale u hu (j - a) (fun i => c i * eval (v i) Q) =
      fun i => coefficientScale u hu j c i * eval (u i • v i) Q := by
  funext i
  rw [LinearEvaluationTransport.homogeneous_eval_smul Q a hQ]
  have hexp : -(j - (a : ℤ)) = -j + a := by omega
  change u i ^ (-(j - (a : ℤ))) * (c i * eval (v i) Q) =
    (u i ^ (-j) * c i) * (u i ^ a * eval (v i) Q)
  rw [hexp, zpow_add₀ (hu i), zpow_natCast]
  ring

end Cylinder.IntegerRepresentativeRelations

end
