module

public import Cylinder.ConicLineCoordinates
public import Cylinder.QuadricLineAlgebra
public import Mathlib.Tactic.IntervalCases

/-! Six actual evaluations determine a homogeneous ternary quadratic.
The coefficient formula is derived directly from its genuine support. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ConicTernaryQuadratic
open MvPolynomial Cylinder.HilbertEvaluation

variable {K : Type*} [Field K]

theorem ternary_quadratic_evaluation (Q : PlaneRing K) (hQ : Q.IsHomogeneous 2)
    (x y z : K) :
    eval ![x, y, z] Q =
      eval ![1, 0, 0] Q * x ^ 2 + eval ![0, 1, 0] Q * y ^ 2 + eval ![0, 0, 1] Q * z ^ 2 +
      (eval ![1, 1, 0] Q - eval ![1, 0, 0] Q - eval ![0, 1, 0] Q) * x * y +
      (eval ![1, 0, 1] Q - eval ![1, 0, 0] Q - eval ![0, 0, 1] Q) * x * z +
      (eval ![0, 1, 1] Q - eval ![0, 1, 0] Q - eval ![0, 0, 1] Q) * y * z := by
  have hterm : ∀ m ∈ Q.support,
      Q.coeff m * (x ^ m 0 * y ^ m 1 * z ^ m 2) =
      (Q.coeff m * ((1 : K) ^ m 0 * 0 ^ m 1 * 0 ^ m 2)) * x ^ 2 +
      (Q.coeff m * ((0 : K) ^ m 0 * 1 ^ m 1 * 0 ^ m 2)) * y ^ 2 +
      (Q.coeff m * ((0 : K) ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * z ^ 2 +
      (Q.coeff m * (1 ^ m 0 * 1 ^ m 1 * 0 ^ m 2) -
        Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 0 ^ m 2) -
        Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 0 ^ m 2)) * x * y +
      (Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 1 ^ m 2) -
        Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 0 ^ m 2) -
        Q.coeff m * (0 ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * x * z +
      (Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 1 ^ m 2) -
        Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 0 ^ m 2) -
        Q.coeff m * (0 ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * y * z := by
    intro m hm
    have hd : m 0 + m 1 + m 2 = 2 := by
      have h := hQ (mem_support_iff.mp hm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three] at h
      exact h
    have h0b : m 0 ≤ 2 := by omega
    have h1b : m 1 ≤ 2 := by omega
    interval_cases h0 : m 0 <;> interval_cases h1 : m 1
    all_goals try omega
    all_goals have h2 : m 2 = 2 - m 0 - m 1 := by omega
    all_goals simp only [h0, h1, h2, Nat.reduceSub, pow_zero, pow_one, one_pow, zero_pow (by decide : 2 ≠ 0),
      zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero, sub_self]
    all_goals ring
  calc
    eval ![x, y, z] Q = ∑ m ∈ Q.support, Q.coeff m * (x ^ m 0 * y ^ m 1 * z ^ m 2) := by
      simp only [eval_eq', Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rfl

    _ = ∑ m ∈ Q.support,
      ((Q.coeff m * ((1 : K) ^ m 0 * 0 ^ m 1 * 0 ^ m 2)) * x ^ 2 +
      (Q.coeff m * ((0 : K) ^ m 0 * 1 ^ m 1 * 0 ^ m 2)) * y ^ 2 +
      (Q.coeff m * ((0 : K) ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * z ^ 2 +
      (Q.coeff m * (1 ^ m 0 * 1 ^ m 1 * 0 ^ m 2) -
        Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 0 ^ m 2) - Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 0 ^ m 2)) * x * y +
      (Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 1 ^ m 2) -
        Q.coeff m * (1 ^ m 0 * 0 ^ m 1 * 0 ^ m 2) - Q.coeff m * (0 ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * x * z +
      (Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 1 ^ m 2) -
        Q.coeff m * (0 ^ m 0 * 1 ^ m 1 * 0 ^ m 2) - Q.coeff m * (0 ^ m 0 * 0 ^ m 1 * 1 ^ m 2)) * y * z) :=
        Finset.sum_congr rfl hterm
    _ = _ := by
      simp only [eval_eq', Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
      rfl

theorem exists_quadratic_coefficients [Infinite K] (Q : PlaneRing K) (hQ : Q.IsHomogeneous 2) :
    ∃ a b c d e f : K, Q = C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 +
      C d * X 0 * X 1 + C e * X 0 * X 2 + C f * X 1 * X 2 := by
  refine ⟨eval ![1, 0, 0] Q, eval ![0, 1, 0] Q, eval ![0, 0, 1] Q,
    eval ![1, 1, 0] Q - eval ![1, 0, 0] Q - eval ![0, 1, 0] Q,
    eval ![1, 0, 1] Q - eval ![1, 0, 0] Q - eval ![0, 0, 1] Q,
    eval ![0, 1, 1] Q - eval ![0, 1, 0] Q - eval ![0, 0, 1] Q, ?_⟩
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, ternary_quadratic_evaluation Q hQ]
  simp only [map_add, map_mul, map_pow, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

end Cylinder.ConicTernaryQuadratic
end
