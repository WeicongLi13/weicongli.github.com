module

public import Cylinder.LocalCharacterData
public import Cylinder.IntegerRepresentativeRelations

/-! Hilbert functions, initial degrees and numerical characters are invariant
under nonzero rescaling of the actual projective point representatives. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalRepresentativeTransport
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas
open Cylinder.LinearEvaluationTransport

variable {K I : Type*} [Field K] [Fintype I]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

theorem evaluationMap_rescaling (v : I → Fin 3 → K) (a : I → K)
    (ha : ∀ i, a i ≠ 0) (d : ℕ) :
    evaluationMap (fun i => a i • v i) d =
      (diagonalEquiv (fun i => a i ^ d) (fun i => pow_ne_zero d (ha i))).toLinearMap.comp
        (evaluationMap v d) := by
  ext P i
  exact homogeneous_eval_smul P.val d P.property (a i) (v i)

theorem hilbert_rescaling (v : I → Fin 3 → K) (a : I → K)
    (ha : ∀ i, a i ≠ 0) (d : ℕ) :
    hilbert (fun i => a i • v i) d = hilbert v d := by
  let E := diagonalEquiv (fun i => a i ^ d) (fun i => pow_ne_zero d (ha i))
  have hr : evaluationSpace (fun i => a i • v i) d = (evaluationSpace v d).map E.toLinearMap := by
    change LinearMap.range _ = (LinearMap.range _).map _
    rw [evaluationMap_rescaling v a ha d, LinearMap.range_comp]
  change finrank K (evaluationSpace (fun i => a i • v i) d) = _
  rw [hr]
  exact LinearEquiv.finrank_map_eq E (evaluationSpace v d)

theorem idealPiece_rescaling (v : I → Fin 3 → K) (a : I → K)
    (ha : ∀ i, a i ≠ 0) (d : ℕ) :
    idealPiece (fun i => a i • v i) d = idealPiece v d := by
  ext P
  change P.val ∈ (vanishingIdeal (fun i => a i • v i)).toIdeal ↔
    P.val ∈ (vanishingIdeal v).toIdeal
  rw [homogeneous_mem_vanishingIdeal _ P.val d P.property,
    homogeneous_mem_vanishingIdeal _ P.val d P.property]
  simp only [homogeneous_eval_smul P.val d P.property]
  exact forall_congr' fun i => mul_eq_zero.trans
    (or_iff_right (pow_ne_zero d (ha i)))

theorem initialDegree_rescaling (v : I → Fin 3 → K) (a : I → K)
    (ha : ∀ i, a i ≠ 0) (e : ℕ) :
    InitialDegree (fun i => a i • v i) e ↔ InitialDegree v e := by
  simp only [InitialDegree, idealPiece_rescaling v a ha]

theorem numericalCharacter_rescaling [Infinite K] (v : I → Fin 3 → K) (a : I → K)
    (ha : ∀ i, a i ≠ 0) :
    numericalCharacter (fun i => a i • v i) = numericalCharacter v := by
  have hH : hilbert (fun i => a i • v i) = hilbert v := funext (hilbert_rescaling v a ha)
  funext i
  change NumericCharacterSequence.character (NumericCharacterSequence.firstDifference
    (hilbert (fun i => a i • v i))) (Fintype.card I) i = _
  rw [hH]
  rfl

theorem nonzero_rescaling (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (a : I → K) (ha : ∀ i, a i ≠ 0) : ∀ i, a i • v i ≠ 0 := by
  intro i hz
  exact (smul_eq_zero.mp hz).elim (ha i) (hv i)

theorem distinct_rescaling (v : I → Fin 3 → K) (hsep : ProjectivelyDistinct v)
    (a : I → K) (ha : ∀ i, a i ≠ 0) : ProjectivelyDistinct (fun i => a i • v i) := by
  intro i j hij c hrep
  apply hsep i j hij ((a j)⁻¹ * c * a i)
  have hh := congrArg (fun x => (a j)⁻¹ • x) hrep
  simpa only [smul_smul, inv_mul_cancel₀ (ha j), one_smul, mul_assoc] using hh

theorem quotient_rescaling (a c u : K) (ha : a ≠ 0) (hu : u ≠ 0) (d q : ℕ) (hqd : q ≤ d) :
    (c / a ^ (d - q)) / (u / a ^ d) = a ^ q * (c / u) := by
  have hpow : a ^ d = a ^ (d - q) * a ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hqd]
  rw [hpow]
  field_simp [ha, hu]

theorem recurrence_rescaling (a : K) (x : ℕ → K) (q : ℕ)
    (hrec : x (q + 2) = x 1 * x (q + 1) - (x 1 ^ 2 - x 2) * x q) :
    a ^ (q + 2) * x (q + 2) = (a * x 1) * (a ^ (q + 1) * x (q + 1)) -
      ((a * x 1) ^ 2 - a ^ 2 * x 2) * (a ^ q * x q) := by
  simp only [pow_add, pow_one]
  linear_combination a ^ q * a ^ 2 * hrec

theorem interpolation_unscaling (a c u : K) (ha : a ≠ 0) (d q : ℕ) (hqd : q ≤ d)
    (v : Fin 3 → K) (Q : PlaneRing K) (hQ : Q.IsHomogeneous q)
    (hscaled : c / a ^ (d - q) = eval (a • v) Q * (u / a ^ d)) :
    c = eval v Q * u := by
  have hpow : a ^ d = a ^ (d - q) * a ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hqd]
  have hfactor : eval (a • v) Q * (u / a ^ d) = (eval v Q * u) / a ^ (d - q) := by
    rw [homogeneous_eval_smul Q q hQ, hpow]
    field_simp [ha]
  rw [hfactor] at hscaled
  exact (div_left_inj' (pow_ne_zero (d - q) ha)).mp hscaled

#print axioms hilbert_rescaling
#print axioms idealPiece_rescaling
#print axioms initialDegree_rescaling
#print axioms numericalCharacter_rescaling
#print axioms nonzero_rescaling
#print axioms distinct_rescaling
#print axioms quotient_rescaling
#print axioms recurrence_rescaling
#print axioms interpolation_unscaling

end Cylinder.LocalRepresentativeTransport
end
