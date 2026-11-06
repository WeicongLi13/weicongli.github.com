import NSDensity.CodePolynomial
import Mathlib.RingTheory.AdjoinRoot

/-! The coefficient-vector identification with the cyclic polynomial quotient. -/

open scoped BigOperators Polynomial

namespace NSDensity.Concrete

noncomputable def wordPolynomialLinear (F : Type*) [Field F] (n : ℕ) :
    (Fin n → F) →ₗ[F] F[X] where
  toFun := wordPolynomial
  map_add' c d := by
    simp [wordPolynomial, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [wordPolynomial, Finset.smul_sum, Polynomial.smul_monomial]

@[simp] theorem wordPolynomialLinear_apply {F : Type*} [Field F] {n : ℕ}
    (c : Fin n → F) : wordPolynomialLinear F n c = wordPolynomial c := rfl

noncomputable def wordQuotient (F : Type*) [Field F] (n : ℕ) :
    (Fin n → F) →ₗ[F] AdjoinRoot (Polynomial.X ^ n - 1 : F[X]) :=
  (AdjoinRoot.mkₐ (Polynomial.X ^ n - 1 : F[X])).toLinearMap.comp
    (wordPolynomialLinear F n)

@[simp] theorem wordQuotient_apply {F : Type*} [Field F] {n : ℕ}
    (c : Fin n → F) : wordQuotient F n c =
      AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]) (wordPolynomial c) := rfl

theorem wordQuotient_injective {F : Type*} [Field F] {n : ℕ} (hn : 0 < n) :
    Function.Injective (wordQuotient F n) := by
  intro c d hcd
  have hz : wordQuotient F n (c - d) = 0 := by rw [map_sub, hcd, sub_self]
  have hdiv : (Polynomial.X ^ n - 1 : F[X]) ∣ wordPolynomial (c - d) :=
    AdjoinRoot.mk_eq_zero.mp hz
  have hdeg : (Polynomial.X ^ n - 1 : F[X]).degree = n := by
    simpa using Polynomial.degree_X_pow_sub_C (R := F) hn (1 : F)
  have hzero : wordPolynomial (c - d) = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hdiv
      (by rw [hdeg]; exact wordPolynomial_degree_lt _)
  have hword : wordPolynomial (c - d) = wordPolynomial (0 : Fin n → F) := by
    simpa [wordPolynomial] using hzero
  exact sub_eq_zero.mp (wordPolynomial_injective hword)

theorem wordPolynomial_coefficients {F : Type*} [Field F] {n : ℕ}
    (p : F[X]) (hp : p.degree < n) :
    wordPolynomial (fun i : Fin n => p.coeff i.val) = p := by
  ext k
  by_cases hk : k < n
  · exact wordPolynomial_coeff _ ⟨k, hk⟩
  · have hnk : (n : WithBot ℕ) ≤ k := by exact_mod_cast Nat.le_of_not_gt hk
    have hwp : (wordPolynomial (fun i : Fin n => p.coeff i.val)).degree < k :=
      (wordPolynomial_degree_lt _).trans_le hnk
    rw [Polynomial.coeff_eq_zero_of_degree_lt hwp,
      Polynomial.coeff_eq_zero_of_degree_lt (hp.trans_le hnk)]

end NSDensity.Concrete
