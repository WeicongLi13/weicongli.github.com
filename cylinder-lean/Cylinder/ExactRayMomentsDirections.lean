module

public import Cylinder.ExactRayMomentsLow
public import Cylinder.PowerEvaluationRelation
public import Cylinder.HilbertEvaluation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! The prime and different-factor hypotheses are derived from actual
nonzero projectively distinct direction representatives. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsDirections
open MvPolynomial Cylinder.HilbertEvaluation
variable {K I E : Type*} [Field K] [Fintype I] [Fintype E]

def directionForm (v : Fin 3 → K) : PlaneRing K := Cylinder.PowerEvaluationRelation.linearForm v

theorem directionForm_eval_basis (v : Fin 3 → K) (j : Fin 3) :
    eval (Pi.single j (1 : K)) (directionForm v) = v j := by
  simp [directionForm, Cylinder.PowerEvaluationRelation.linearForm, Pi.single_apply, eq_comm]

theorem directionForm_nonzero (v : Fin 3 → K) (hv : v ≠ 0) : directionForm v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hz := congrArg (eval (Pi.single j (1 : K))) h
  simpa only [directionForm_eval_basis, map_zero, Pi.zero_apply] using hz

theorem directionForm_homogeneous (v : Fin 3 → K) : (directionForm v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum Finset.univ _ 1
  intro j _
  exact isHomogeneous_C_mul_X _ _

theorem directionForm_degree (v : Fin 3 → K) (hv : v ≠ 0) : (directionForm v).totalDegree = 1 :=
  (directionForm_homogeneous v).totalDegree (directionForm_nonzero v hv)

theorem directionForm_prime (v : Fin 3 → K) (hv : v ≠ 0) : Prime (directionForm v) := by
  apply Irreducible.prime
  apply irreducible_of_totalDegree_eq_one (directionForm_degree v hv)
  intro c hc
  apply isUnit_iff_ne_zero.mpr
  intro hz
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero (directionForm_nonzero v hv)
  have hd := hc m
  rw [hz, zero_dvd_iff] at hd
  exact hm hd

omit [Fintype I] in
theorem directionForms_not_dvd (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (i k : I) (hik : i ≠ k) :
    ¬directionForm (v i) ∣ directionForm (v k) := by
  rintro ⟨Q, hQ⟩
  have hQ0 : Q ≠ 0 := by
    intro hz
    apply directionForm_nonzero (v k) (hv k)
    rw [hQ, hz, mul_zero]
  have hdegree : 1 = 1 + Q.totalDegree := by
    have h := congrArg (fun P : PlaneRing K => P.totalDegree) hQ
    rw [directionForm_degree _ (hv k),
      totalDegree_mul_of_isDomain (directionForm_nonzero _ (hv i)) hQ0,
      directionForm_degree _ (hv i)] at h
    exact h
  have hdegree0 : Q.totalDegree = 0 := by omega
  have hQc : Q = C (Q.coeff 0) := (totalDegree_eq_zero_iff_eq_C (p := Q)).mp hdegree0
  apply hsep i k hik (Q.coeff 0)
  funext j
  change v k j = Q.coeff 0 * v i j
  have h := congrArg (eval (Pi.single j (1 : K))) hQ
  rw [hQc, map_mul, eval_C, directionForm_eval_basis, directionForm_eval_basis] at h
  simpa only [mul_comm] using h

theorem actual_direction_product_low_moments
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (dir : E → I) (c t : E → K) (P : Polynomial (PlaneRing K))
    (hprod : P = Cylinder.ExactRayMomentsLow.actualNumerator dir (fun i => directionForm (v i)) c t)
    (w : ℕ) (horder : Polynomial.X ^ w ∣ P) (j : ℕ) (hj : j < w) :
    ∀ i, Cylinder.ExactRayMomentsLow.moment dir c t i j = 0 :=
  Cylinder.ExactRayMomentsLow.normalized_product_low_moments dir _
    (fun i => directionForm_prime (v i) (hv i)) (directionForms_not_dvd v hv hsep)
    c t P hprod w horder j hj

end Cylinder.ExactRayMomentsDirections
end
