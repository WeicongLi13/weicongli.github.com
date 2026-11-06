module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Prime.Defs
public import Lean.Elab.Tactic.Omega

/-!
# The denominator-factor degree bound in Proposition `prop:poles`

In the actual polynomial ring in three variables over a field, a prime
polynomial is nonconstant. Its multiplicity in a nonzero polynomial is
therefore at most that polynomial's total degree.
-/

@[expose] public section

namespace Cylinder.PolynomialDegree

variable {K : Type*} [Field K]

/-- A prime polynomial over a field has positive total degree. This is
derived from primality, rather than imposed as an extra degree hypothesis. -/
theorem prime_totalDegree_pos (π : MvPolynomial (Fin 3) K) (hπ : Prime π) :
    1 ≤ π.totalDegree := by
  by_contra hn
  have hz : π.totalDegree = 0 := Nat.eq_zero_of_not_pos (by omega)
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
  have hcoeff : π.coeff 0 ≠ 0 := by
    intro he
    apply hπ.ne_zero
    rw [hc, he, map_zero]
  apply hπ.not_isUnit
  rw [hc]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

/-- Over a field, multiplication adds total degrees of nonzero factors,
so taking a nonzero polynomial to the `n`th power multiplies its degree. -/
theorem totalDegree_pow_exact (π : MvPolynomial (Fin 3) K) (hπ : π ≠ 0) (n : ℕ) :
    (π ^ n).totalDegree = n * π.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain (pow_ne_zero n hπ) hπ, ih,
        Nat.succ_mul]

/-- The exponent of a prime divisor of a nonzero three-variable polynomial
is bounded by total degree. This supplies `a ≤ r` in the paper. -/
theorem prime_power_dvd_degree_bound
    (π A : MvPolynomial (Fin 3) K) (n : ℕ)
    (hπ : Prime π) (hA : A ≠ 0) (hdiv : π ^ n ∣ A) :
    n ≤ A.totalDegree := by
  have hdegree := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hA
  rw [totalDegree_pow_exact π hπ.ne_zero n] at hdegree
  calc
    n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * π.totalDegree := Nat.mul_le_mul_left n (prime_totalDegree_pos π hπ)
    _ ≤ A.totalDegree := hdegree

end Cylinder.PolynomialDegree
