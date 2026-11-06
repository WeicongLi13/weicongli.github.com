module

public import Cylinder.PowerEvaluationRelation
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Equal projections in n distinct directions give all mixed moments of
degree below n. The projections are genuine bijections between the two sets. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ThreeNetMomentPolynomials

open Polynomial

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def affinePower (x y : K) (r : ℕ) : Polynomial K := (C x * X + C y) ^ r

theorem affinePower_degree (x y : K) (r : ℕ) : (affinePower x y r).natDegree ≤ r := by
  have hlin : (C x * X + C y : Polynomial K).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le.trans (by simp))
    · simp
  exact (natDegree_pow_le.trans (Nat.mul_le_mul_left r hlin)).trans_eq (by simp)

theorem affinePower_coeff (x y : K) (r i : ℕ) :
    (affinePower x y r).coeff i = (r.choose i : K) * x ^ i * y ^ (r - i) := by
  have heq : affinePower x y r = ((X + C y) ^ r).comp (C x * X) := by
    simp only [affinePower, pow_comp, add_comp, X_comp, C_comp]
  rw [heq, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

def momentPolynomial (a : I → Fin 2 → K) (b : J → Fin 2 → K) (r : ℕ) : Polynomial K :=
  (∑ i, affinePower (a i 0) (a i 1) r) - ∑ j, affinePower (b j 0) (b j 1) r

theorem momentPolynomial_degree (a : I → Fin 2 → K) (b : J → Fin 2 → K) (r : ℕ) :
    (momentPolynomial a b r).natDegree ≤ r := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_sum_le_of_forall_le _ _ (fun i _ => affinePower_degree _ _ r)
  · exact natDegree_sum_le_of_forall_le _ _ (fun j _ => affinePower_degree _ _ r)

theorem momentPolynomial_eval_zero (a : I → Fin 2 → K) (b : J → Fin 2 → K)
    (r : ℕ) (t : K) (e : I ≃ J)
    (he : ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1) :
    (momentPolynomial a b r).eval t = 0 := by
  have hsum : (∑ i, (t * a i 0 + a i 1) ^ r) =
      ∑ j, (t * b j 0 + b j 1) ^ r := by
    calc
      _ = ∑ i, (t * b (e i) 0 + b (e i) 1) ^ r := Finset.sum_congr rfl (fun i _ => congrArg (· ^ r) (he i))
      _ = _ := e.sum_comp (fun j => (t * b j 0 + b j 1) ^ r)
  simpa only [momentPolynomial, affinePower, eval_sub, eval_finsetSum, eval_pow,
    eval_add, eval_mul, eval_C, eval_X, mul_comm, sub_eq_zero] using hsum

theorem momentPolynomial_zero (a : I → Fin 2 → K) (b : J → Fin 2 → K)
    (D : Finset K) (r : ℕ) (hr : r < D.card)
    (hmatch : ∀ t ∈ D, ∃ e : I ≃ J,
      ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1) :
    momentPolynomial a b r = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ D
  · intro t ht
    obtain ⟨e, he⟩ := hmatch t ht
    exact momentPolynomial_eval_zero a b r t e he
  · exact (momentPolynomial_degree a b r).trans_lt hr

theorem choose_cast_ne_zero (p r i : ℕ) [Fact p.Prime] [CharP K p]
    (hr : r < p) (hi : i ≤ r) : (r.choose i : K) ≠ 0 := by
  intro hz
  have hchoose : r.choose i ∣ Nat.factorial r :=
    ⟨Nat.factorial i * Nat.factorial (r - i), by
      simpa only [mul_assoc] using (Nat.choose_mul_factorial_mul_factorial hi).symm⟩
  have hdvd := (CharP.cast_eq_zero_iff K p (r.choose i)).mp hz
  have hp := ((Fact.out : p.Prime).dvd_factorial).mp (dvd_trans hdvd hchoose)
  omega

theorem mixed_moments_equal (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : I → Fin 2 → K) (b : J → Fin 2 → K) (D : Finset K)
    (hDp : D.card ≤ p)
    (hmatch : ∀ t ∈ D, ∃ e : I ≃ J,
      ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1)
    (i j : ℕ) (hij : i + j < D.card) :
    (∑ k, (a k 0) ^ i * (a k 1) ^ j) = ∑ k, (b k 0) ^ i * (b k 1) ^ j := by
  have hz := momentPolynomial_zero a b D (i + j) hij hmatch
  have hcoeff := congrArg (fun F : Polynomial K => F.coeff i) hz
  simp only [momentPolynomial, coeff_sub, finsetSum_coeff, affinePower_coeff,
    Nat.add_sub_cancel_left, coeff_zero] at hcoeff
  simp_rw [mul_assoc] at hcoeff
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hcoeff
  apply mul_left_cancel₀ (choose_cast_ne_zero (K := K) p (i + j) i (by omega) (by omega))
  exact sub_eq_zero.mp hcoeff

end Cylinder.ThreeNetMomentPolynomials

end
