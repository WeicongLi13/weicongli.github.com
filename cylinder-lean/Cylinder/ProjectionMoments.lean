module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Projection moments over the prime field

The proof uses the one-variable polynomial
`Q_n(t) = sum m(x,y) * (x + t*y)^n`, for each `n < p`.
Line sums make all its evaluations zero. Its degree is less than the
field cardinality, so it is zero as a polynomial. Comparing coefficients
and cancelling the nonzero binomial coefficient proves every required
mixed moment. This avoids assuming that the projection polynomial or
any of its coefficients vanishes.
-/

@[expose] public section

namespace Cylinder.ProjectionMoments

open scoped BigOperators
open Finset Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev PlanePoint := ZMod p × ZMod p

/-- Every affine line with a nonzero normal has total weight zero. -/
def LineSumsZero (m : PlanePoint p → ZMod p) : Prop :=
  ∀ a b : ZMod p, (a, b) ≠ (0, 0) → ∀ c : ZMod p,
    ∑ z ∈ Finset.univ.filter (fun z : PlanePoint p => a * z.1 + b * z.2 = c), m z = 0

/-- Summing first over the fibers of a nonzero linear form shows that
every function of that form has weighted sum zero. -/
theorem weighted_linear_sum_zero
    (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m)
    (a b : ZMod p) (hab : (a, b) ≠ (0, 0)) (φ : ZMod p → ZMod p) :
    ∑ z : PlanePoint p, m z * φ (a * z.1 + b * z.2) = 0 := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun z : PlanePoint p => a * z.1 + b * z.2)
    (fun z => m z * φ (a * z.1 + b * z.2))]
  apply Finset.sum_eq_zero
  intro c _
  calc
    (∑ z ∈ Finset.univ.filter (fun z : PlanePoint p => a * z.1 + b * z.2 = c),
        m z * φ (a * z.1 + b * z.2)) =
      ∑ z ∈ Finset.univ.filter (fun z : PlanePoint p => a * z.1 + b * z.2 = c),
        m z * φ c := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [(Finset.mem_filter.mp hz).2]
    _ = (∑ z ∈ Finset.univ.filter (fun z : PlanePoint p => a * z.1 + b * z.2 = c),
        m z) * φ c := (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hm a b hab c, zero_mul]

/-- The total-weight condition follows already from the parallel line
partition, so it need not be imposed again. -/
theorem total_weight_zero (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m) :
    ∑ z : PlanePoint p, m z = 0 := by
  simpa using weighted_linear_sum_zero p m hm 1 0 (by simp) (fun _ => 1)

/-- This is the evaluation identity for the paper's affine projection
polynomial, valid also when the linear part is zero. -/
theorem affine_power_sum_zero
    (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m)
    (T a b : ZMod p) (n : ℕ) :
    ∑ z : PlanePoint p, m z * (T + a * z.1 + b * z.2) ^ n = 0 := by
  by_cases hab : (a, b) = (0, 0)
  · have ha : a = 0 := congrArg Prod.fst hab
    have hb : b = 0 := congrArg Prod.snd hab
    simp only [ha, hb, zero_mul, add_zero]
    rw [← Finset.sum_mul, total_weight_zero p m hm, zero_mul]
  · simpa only [add_assoc] using
      weighted_linear_sum_zero p m hm a b hab (fun c => (T + c) ^ n)

/-- The polynomial used to recover moments of total degree `n`. -/
noncomputable def slopePolynomial (m : PlanePoint p → ZMod p) (n : ℕ) :
    Polynomial (ZMod p) :=
  ∑ z : PlanePoint p, C (m z) * (C z.1 + C z.2 * X) ^ n

theorem slopePolynomial_eval_zero
    (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m) (n : ℕ) (t : ZMod p) :
    (slopePolynomial p m n).eval t = 0 := by
  rw [slopePolynomial, Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  simpa only [one_mul, mul_comm t] using
    weighted_linear_sum_zero p m hm 1 t (by simp) (fun c => c ^ n)

theorem slopePolynomial_degree_le (m : PlanePoint p → ZMod p) (n : ℕ) :
    (slopePolynomial p m n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z _
  apply le_trans (Polynomial.natDegree_C_mul_le _ _) 
  apply le_trans Polynomial.natDegree_pow_le
  have hl : (C z.1 + C z.2 * X : Polynomial (ZMod p)).natDegree ≤ 1 := by
    apply le_trans (Polynomial.natDegree_add_le _ _)
    apply max_le
    · simp
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  simpa using Nat.mul_le_mul_left n hl

theorem slopePolynomial_eq_zero
    (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m) (n : ℕ) (hn : n < p) :
    slopePolynomial p m n = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
    (fun t => slopePolynomial_eval_zero p m hm n t)
  simpa only [ZMod.card] using lt_of_le_of_lt (slopePolynomial_degree_le p m n) hn

/-- A factorial strictly below the characteristic is nonzero in the field. -/
theorem factorial_cast_ne_zero (n : ℕ) (hn : n < p) :
    (n.factorial : ZMod p) ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply mul_ne_zero
      · intro hz
        have hdiv := (ZMod.natCast_eq_zero_iff (n + 1) p).mp hz
        exact (not_le_of_gt hn) (Nat.le_of_dvd (by omega) hdiv)
      · exact ih (by omega)

/-- Every binomial coefficient in a row strictly below the characteristic
is nonzero in the prime field. -/
theorem choose_cast_ne_zero (n j : ℕ) (hn : n < p) (hj : j ≤ n) :
    (n.choose j : ZMod p) ≠ 0 := by
  intro hz
  have hfact : (n.choose j : ZMod p) * (j.factorial : ZMod p) *
      ((n - j).factorial : ZMod p) = (n.factorial : ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun k : ℕ => (k : ZMod p))
      (Nat.choose_mul_factorial_mul_factorial hj)
  rw [hz, zero_mul, zero_mul] at hfact
  exact factorial_cast_ne_zero p n hn hfact.symm

/-- The coefficient of the `j`th power in a linear polynomial to the `n`th
power; the formula remains valid when either constant is zero. -/
theorem coeff_linear_pow (x y : ZMod p) (n j : ℕ) (hj : j ≤ n) :
    ((C x + C y * X : Polynomial (ZMod p)) ^ n).coeff j =
      x ^ (n - j) * y ^ j * (n.choose j : ZMod p) := by
  rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
  simp only [mul_pow, ← C_pow, ← C_eq_natCast, coeff_mul_C, coeff_C_mul]
  rw [Finset.sum_eq_single j]
  · simp only [coeff_X_pow_self, mul_one]
    ring
  · intro k _ hkj
    simp [coeff_X_pow, Ne.symm hkj]
  · intro hjnot
    exact False.elim (hjnot (Finset.mem_range.mpr (by omega)))

theorem slopePolynomial_coeff (m : PlanePoint p → ZMod p) (n j : ℕ) (hj : j ≤ n) :
    (slopePolynomial p m n).coeff j =
      (n.choose j : ZMod p) *
        ∑ z : PlanePoint p, m z * z.1 ^ (n - j) * z.2 ^ j := by
  rw [slopePolynomial, Polynomial.finsetSum_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Polynomial.coeff_C_mul, coeff_linear_pow p z.1 z.2 n j hj]
  ring

/-- All mixed moments up to total degree `p - 1` vanish. The line-sum
hypothesis is used to derive polynomial vanishing, rather than replacing
that crucial conclusion with a hypothesis. -/
theorem mixed_moment_zero
    (m : PlanePoint p → ZMod p) (hm : LineSumsZero p m)
    (i j : ℕ) (hij : i + j ≤ p - 1) :
    ∑ z : PlanePoint p, m z * z.1 ^ i * z.2 ^ j = 0 := by
  have hn : i + j < p := by have hp := (Fact.out : p.Prime).two_le; omega
  have hcoeff := congrArg (fun P : Polynomial (ZMod p) => P.coeff j)
    (slopePolynomial_eq_zero p m hm (i + j) hn)
  rw [slopePolynomial_coeff p m (i + j) j (by omega), coeff_zero] at hcoeff
  have hchoose := choose_cast_ne_zero p (i + j) j hn (by omega)
  have hmoment := (mul_eq_zero.mp hcoeff).resolve_left hchoose
  simpa only [Nat.add_sub_cancel] using hmoment

end Cylinder.ProjectionMoments
