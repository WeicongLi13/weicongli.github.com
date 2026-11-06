module

public import Cylinder.QuadricRayAlgebra
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.IntervalCases

/-! A homogeneous binary quadric vanishing at both coordinate points and
a third point with nonzero coordinates is zero. The restriction to a true
linear span then vanishes identically, in every characteristic. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.QuadricLineAlgebra

open MvPolynomial

variable {K : Type*} [Field K]

theorem binary_quadric_evaluation (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous 2)
    (x y : K) :
    eval ![x, y] P = eval ![1, 0] P * x ^ 2 + eval ![0, 1] P * y ^ 2 +
      (eval ![1, 1] P - eval ![1, 0] P - eval ![0, 1] P) * x * y := by
  have hterm : ∀ m ∈ P.support,
      P.coeff m * (x ^ m 0 * y ^ m 1) =
      (P.coeff m * ((1 : K) ^ m 0 * 0 ^ m 1)) * x ^ 2 +
      (P.coeff m * ((0 : K) ^ m 0 * 1 ^ m 1)) * y ^ 2 +
      (P.coeff m * (1 ^ m 0 * 1 ^ m 1) -
        P.coeff m * (1 ^ m 0 * 0 ^ m 1) - P.coeff m * (0 ^ m 0 * 1 ^ m 1)) * x * y := by
    intro m hm
    have hdegree : m 0 + m 1 = 2 := by
      have h := hP (mem_support_iff.mp hm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
      exact h
    have hm0 : m 0 ≤ 2 := by omega
    interval_cases h0 : m 0
    · have h1 : m 1 = 2 := by omega
      simp [h1]
    · have h1 : m 1 = 1 := by omega
      simp [h1, mul_assoc]
    · have h1 : m 1 = 0 := by omega
      simp [h1]
  calc
    eval ![x, y] P = ∑ m ∈ P.support, P.coeff m * (x ^ m 0 * y ^ m 1) := by
      simp only [eval_eq', Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    _ = ∑ m ∈ P.support,
        ((P.coeff m * ((1 : K) ^ m 0 * 0 ^ m 1)) * x ^ 2 +
        (P.coeff m * ((0 : K) ^ m 0 * 1 ^ m 1)) * y ^ 2 +
        (P.coeff m * (1 ^ m 0 * 1 ^ m 1) -
          P.coeff m * (1 ^ m 0 * 0 ^ m 1) - P.coeff m * (0 ^ m 0 * 1 ^ m 1)) * x * y) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      simp only [eval_eq', Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]

theorem binary_quadric_three_zeros [Infinite K] (P : MvPolynomial (Fin 2) K) (hP : P.IsHomogeneous 2)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hfirst : eval ![1, 0] P = 0) (hsecond : eval ![0, 1] P = 0)
    (hthird : eval ![x, y] P = 0) : P = 0 := by
  have hmiddle : eval ![1, 1] P = 0 := by
    rw [binary_quadric_evaluation P hP x y, hfirst, hsecond] at hthird
    simp only [zero_mul, zero_add, sub_zero] at hthird
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hthird).resolve_right hy)).resolve_right hx
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, binary_quadric_evaluation P hP, hfirst, hsecond, hmiddle]
  simp

def lineRestriction {σ : Type*} (Q : MvPolynomial σ K) (u v : σ → K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun j => C (u j) * X 0 + C (v j) * X 1) Q

theorem lineRestriction_homogeneous {σ : Type*} (Q : MvPolynomial σ K)
    (hQ : Q.IsHomogeneous 2) (u v : σ → K) : (lineRestriction Q u v).IsHomogeneous 2 := by
  simpa only [lineRestriction, one_mul] using hQ.aeval
    (fun j => C (u j) * X (0 : Fin 2) + C (v j) * X 1)
    (fun j => (isHomogeneous_C_mul_X (u j) 0).add (isHomogeneous_C_mul_X (v j) 1))

theorem lineRestriction_eval {σ : Type*} (Q : MvPolynomial σ K) (u v : σ → K) (x y : K) :
    eval ![x, y] (lineRestriction Q u v) = eval (x • u + y • v) Q := by
  change aeval ![x, y] (aeval (fun j => C (u j) * X 0 + C (v j) * X 1) Q) = _
  rw [comp_aeval_apply]
  change eval (fun j => eval ![x, y] (C (u j) * X 0 + C (v j) * X 1)) Q = _
  have he : (fun j => eval ![x, y] (C (u j) * X 0 + C (v j) * X 1)) = x • u + y • v := by
    funext j
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he]

theorem vanish_on_span_of_three [Infinite K] {σ : Type*} (Q : MvPolynomial σ K)
    (hQ : Q.IsHomogeneous 2) (u v : σ → K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : eval u Q = 0) (hv : eval v Q = 0) (hw : eval (a • u + b • v) Q = 0) :
    ∀ x y : K, eval (x • u + y • v) Q = 0 := by
  have hline : lineRestriction Q u v = 0 := binary_quadric_three_zeros _
    (lineRestriction_homogeneous Q hQ u v) a b ha hb
    (by simpa only [lineRestriction_eval, one_smul, zero_smul, add_zero] using hu)
    (by simpa only [lineRestriction_eval, one_smul, zero_smul, zero_add] using hv)
    (by rwa [lineRestriction_eval])
  intro x y
  rw [← lineRestriction_eval, hline, map_zero]

end Cylinder.QuadricLineAlgebra

end
