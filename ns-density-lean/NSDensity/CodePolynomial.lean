import NSDensity.CodeModelGenerated
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Ideal.Span

open scoped BigOperators

namespace NSDensity.Concrete

/-- The usual coefficient-polynomial representation of a length-n word. -/
noncomputable def wordPolynomial {F : Type*} [Field F] {n : ℕ} (c : Fin n → F) : Polynomial F :=
  ∑ i : Fin n, Polynomial.monomial i.val (c i)

@[simp]
theorem wordPolynomial_coeff {F : Type*} [Field F] {n : ℕ} (c : Fin n → F) (i : Fin n) :
    (wordPolynomial c).coeff i.val = c i := by
  classical
  simp only [wordPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Fin.val_ne_of_ne hji]
  · simp

theorem wordPolynomial_injective {F : Type*} [Field F] {n : ℕ} :
    Function.Injective (wordPolynomial : (Fin n → F) → Polynomial F) := by
  intro c d h
  funext i
  simpa using congrArg (fun f : Polynomial F => f.coeff i.val) h

theorem wordPolynomial_degree_lt {F : Type*} [Field F] {n : ℕ} (c : Fin n → F) :
    (wordPolynomial c).degree < n := by
  classical
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  simp only [wordPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  simp [Nat.ne_of_lt (lt_of_lt_of_le i.isLt hk)]

theorem aeval_wordPolynomial {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (a : E) (c : Fin n → F) :
    Polynomial.aeval a (wordPolynomial c) = ∑ i, c i • a ^ i.val := by
  simp [wordPolynomial, Algebra.smul_def]

/-- The root-relation code is exactly the coefficient representation of
the polynomials divisible by the irreducible check polynomial. -/
theorem mem_relationCode_iff_minpoly_dvd {E : Type*} [Field E] (F : Subfield E)
    {n : ℕ} (a : E) (c : Fin n → F) :
    c ∈ relationCode F (fun i : Fin n => a ^ i.val) ↔
      minpoly F a ∣ wordPolynomial c := by
  rw [minpoly.dvd_iff, aeval_wordPolynomial]
  rfl

theorem mem_relationCode_iff_checkIdeal {E : Type*} [Field E] (F : Subfield E)
    {n : ℕ} (a : E) (c : Fin n → F) :
    c ∈ relationCode F (fun i : Fin n => a ^ i.val) ↔
      wordPolynomial c ∈ Ideal.span ({minpoly F a} : Set (Polynomial F)) := by
  rw [Ideal.mem_span_singleton]
  exact mem_relationCode_iff_minpoly_dvd F a c

theorem rootCheck_irreducible {E : Type*} [Field E] [Finite E]
    (F : Subfield E) (a : E) : Irreducible (minpoly F a) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) a)

/-- The order of the irreducible check polynomial is exactly the order
of the chosen root. Thus an exact-order root gives the nondegeneracy
condition used in the paper. -/
theorem rootCheck_dvd_X_pow_sub_one_iff {E : Type*} [Field E]
    (F : Subfield E) {a : E} {n k : ℕ} (ha : orderOf a = n) :
    minpoly F a ∣ (Polynomial.X ^ k - 1 : Polynomial F) ↔ n ∣ k := by
  rw [minpoly.dvd_iff, map_sub, Polynomial.aeval_X_pow, map_one, sub_eq_zero,
    ← orderOf_dvd_iff_pow_eq_one, ha]

theorem rootCheck_dvd_cyclicModulus {E : Type*} [Field E]
    (F : Subfield E) {a : E} {n : ℕ} (ha : orderOf a = n) :
    minpoly F a ∣ (Polynomial.X ^ n - 1 : Polynomial F) :=
  (rootCheck_dvd_X_pow_sub_one_iff F ha).2 (dvd_refl n)

/-- Inverting the root retains the exact length, also in a field viewed
as a multiplicative monoid with zero. -/
theorem inverse_root_orderOf {E : Type*} [Field E] (a : E) :
    orderOf a⁻¹ = orderOf a := by
  simp [orderOf_eq_orderOf_iff]

end NSDensity.Concrete
