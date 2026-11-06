module

public import Cylinder.AffinePointEvaluation
public import Cylinder.PlaneHomogenization
public import Cylinder.PowerEvaluationRelation

/-! Coefficient vectors are actual dual functionals on the finite point
function space. Their affine filtered relations coincide with genuine
homogeneous relations on the normalized projective representatives. -/

@[expose] public section
noncomputable section

namespace Cylinder.FiniteEvaluationDuality

open Module MvPolynomial Finset
open Cylinder.PlaneBinaryReduction Cylinder.AffinePointEvaluation
open Cylinder.PlaneHomogenization Cylinder.CurvePolarLocal
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

def coefficientDualMap : (I → K) →ₗ[K] Dual K (I → K) where
  toFun c :=
    { toFun := fun w => ∑ i, c i * w i
      map_add' := by intro w z; simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := by intro k w; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, mul_sum, RingHom.id_apply] }
  map_add' := by
    intro c d
    apply LinearMap.ext
    intro w
    change (∑ i, (c i + d i) * w i) = (∑ i, c i * w i) + ∑ i, d i * w i
    simp only [add_mul, sum_add_distrib]
  map_smul' := by
    intro k c
    apply LinearMap.ext
    intro w
    change (∑ i, (k * c i) * w i) = k * ∑ i, c i * w i
    simp only [mul_assoc, mul_sum]

theorem coefficientDualMap_injective : Function.Injective (coefficientDualMap (K := K) (I := I)) := by
  intro c d hcd
  funext i
  have h := congrArg (fun F : Dual K (I → K) => F (Pi.single i 1)) hcd
  simpa [coefficientDualMap, Pi.single_apply] using h

theorem coefficientDualMap_surjective : Function.Surjective (coefficientDualMap (K := K) (I := I)) := by
  intro F
  refine ⟨fun i => F (Pi.single i 1), ?_⟩
  apply LinearMap.ext
  intro w
  have hw : w = ∑ i, w i • (Pi.single i (1 : K) : I → K) := by
    funext j
    simp [Pi.single_apply]
  change (∑ i, F (Pi.single i 1) * w i) = F w
  calc
    _ = ∑ i, w i * F (Pi.single i 1) := by apply sum_congr rfl; intro i _; ring
    _ = F (∑ i, w i • Pi.single i 1) := by simp [map_smul, smul_eq_mul]
    _ = F w := congrArg F hw.symm

def coefficientsEquivDual : (I → K) ≃ₗ[K] Dual K (I → K) :=
  LinearEquiv.ofBijective coefficientDualMap ⟨coefficientDualMap_injective, coefficientDualMap_surjective⟩

def filteredPolynomialEvaluation (v : I → Fin 2 → K) (j : ℕ) :
    restrictTotalDegree (Fin 2) K j →ₗ[K] (I → K) :=
  (polynomialEvaluation v).toLinearMap.comp (restrictTotalDegree (Fin 2) K j).subtype

def coefficientRelations (v : I → Fin 2 → K) (j : ℕ) : Submodule K (I → K) :=
  (LinearMap.range (filteredPolynomialEvaluation v j)).dualAnnihilator.comap coefficientDualMap

theorem mem_coefficientRelations (v : I → Fin 2 → K) (j : ℕ) (c : I → K) :
    c ∈ coefficientRelations v j ↔ ∀ P : BinaryRing K, P.totalDegree ≤ j →
      ∑ i, c i * eval (v i) P = 0 := by
  change coefficientDualMap c ∈ (LinearMap.range (filteredPolynomialEvaluation v j)).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h P hP
    exact h _ ⟨⟨P, (mem_restrictTotalDegree _ _ _).mpr hP⟩, rfl⟩
  · intro h w hw
    obtain ⟨P, rfl⟩ := hw
    exact h P.val ((mem_restrictTotalDegree _ _ _).mp P.property)

def normalizedPoints (v : I → Fin 2 → K) : I → Option (Fin 2) → K :=
  fun i x => x.elim 1 (v i)

/-- These are exactly the manuscript's homogeneous degree-j coefficient
relations on the actual normalized points. -/
theorem mem_coefficientRelations_iff_homogeneous (v : I → Fin 2 → K) (j : ℕ) (c : I → K) :
    c ∈ coefficientRelations v j ↔ PowerEvaluationRelation.Relation (normalizedPoints v) c j := by
  rw [mem_coefficientRelations]
  constructor
  · intro h F hF
    have hdeg : (dehomogenize F).totalDegree ≤ j :=
      (dehomogenize_totalDegree_le F).trans hF.totalDegree_le
    have hh := h (dehomogenize F) hdeg
    change (∑ i, c i * eval (fun x => x.elim 1 (v i)) F) = 0
    simpa only [eval_dehomogenize] using hh
  · intro h P hP
    have hh := h (homogenize j P) (homogenize_homogeneous j P hP)
    have heval (i : I) : eval (normalizedPoints v i) (homogenize j P) = eval (v i) P := by
      change eval (fun x => x.elim 1 (v i)) (homogenize j P) = eval (v i) P
      rw [← eval_dehomogenize, dehomogenize_homogenize]
    simpa only [heval] using hh

#print axioms coefficientsEquivDual
#print axioms mem_coefficientRelations_iff_homogeneous

end Cylinder.FiniteEvaluationDuality

end
