module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Restricting a plane polynomial to an affine line

The restriction is an actual one-variable polynomial. Its degree bound
and top coefficient are proved from the monomial expansion, including
directions with zero coordinates and polynomials of degree zero.
-/

@[expose] public section

namespace Cylinder.AffineLinePolynomial

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K]

noncomputable def affineLinear (a v : K) : Polynomial K := C a + C v * X

noncomputable def linePolynomial (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K) :
    Polynomial K :=
  P.eval₂ Polynomial.C (fun i => affineLinear (a i) (v i))

theorem affineLinear_degree_le (a v : K) : (affineLinear a v).natDegree ≤ 1 := by
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · simp
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)

theorem affineLinear_pow_degree_le (a v : K) (n : ℕ) :
    (affineLinear a v ^ n).natDegree ≤ n := by
  apply le_trans Polynomial.natDegree_pow_le
  simpa using Nat.mul_le_mul_left n (affineLinear_degree_le a v)

theorem affineLinear_pow_top_coeff (a v : K) (n : ℕ) :
    (affineLinear a v ^ n).coeff n = v ^ n := by
  have h := Polynomial.coeff_pow_of_natDegree_le (n := 1) (m := n)
    (affineLinear_degree_le a v)
  simpa [affineLinear] using h

theorem linePolynomial_eval (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K) (t : K) :
    (linePolynomial P a v).eval t = MvPolynomial.eval (fun i => a i + t * v i) P := by
  change (Polynomial.evalRingHom t)
    (MvPolynomial.eval₂ Polynomial.C (fun i => affineLinear (a i) (v i)) P) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    ext c
    simp
  rw [hC]
  change MvPolynomial.eval (fun i => (affineLinear (a i) (v i)).eval t) P = _
  have he : (fun i => (affineLinear (a i) (v i)).eval t) =
      (fun i => a i + t * v i) := by
    funext i
    simp only [affineLinear, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    rw [mul_comm (v i) t]
  rw [he]

theorem linePolynomial_expansion (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K) :
    linePolynomial P a v = ∑ s ∈ P.support, C (P.coeff s) *
      (affineLinear (a 0) (v 0) ^ s 0 * affineLinear (a 1) (v 1) ^ s 1) := by
  rw [linePolynomial, MvPolynomial.eval₂_eq']
  simp only [Fin.prod_univ_two]

theorem monomial_line_degree_le
    (c : K) (s : Fin 2 →₀ ℕ) (a v : Fin 2 → K) :
    (C c * (affineLinear (a 0) (v 0) ^ s 0 *
      affineLinear (a 1) (v 1) ^ s 1)).natDegree ≤ s.degree := by
  apply le_trans (Polynomial.natDegree_C_mul_le _ _)
  apply le_trans Polynomial.natDegree_mul_le
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  exact add_le_add (affineLinear_pow_degree_le _ _ _) (affineLinear_pow_degree_le _ _ _)

theorem linePolynomial_degree_le (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K) :
    (linePolynomial P a v).natDegree ≤ P.totalDegree := by
  rw [linePolynomial_expansion]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply le_trans (monomial_line_degree_le _ _ _ _)
  exact MvPolynomial.le_totalDegree hs

theorem monomial_line_top_coeff
    (c : K) (s : Fin 2 →₀ ℕ) (a v : Fin 2 → K) :
    (C c * (affineLinear (a 0) (v 0) ^ s 0 *
      affineLinear (a 1) (v 1) ^ s 1)).coeff s.degree =
        c * (v 0 ^ s 0 * v 1 ^ s 1) := by
  rw [Polynomial.coeff_C_mul, Finsupp.degree_eq_sum, Fin.sum_univ_two,
    Polynomial.coeff_mul_add_eq_of_natDegree_le
      (affineLinear_pow_degree_le _ _ _) (affineLinear_pow_degree_le _ _ _),
    affineLinear_pow_top_coeff, affineLinear_pow_top_coeff]

theorem monomial_line_coeff_of_degree_le
    (c : K) (s : Fin 2 →₀ ℕ) (a v : Fin 2 → K) (D : ℕ) (hD : s.degree ≤ D) :
    (C c * (affineLinear (a 0) (v 0) ^ s 0 *
      affineLinear (a 1) (v 1) ^ s 1)).coeff D =
      if s.degree = D then c * (v 0 ^ s 0 * v 1 ^ s 1) else 0 := by
  by_cases he : s.degree = D
  · rw [← he, ite_eq_left rfl]
    exact monomial_line_top_coeff c s a v
  · rw [ite_eq_right he]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (monomial_line_degree_le c s a v) (lt_of_le_of_ne hD he))

/-- The coefficient at the original total degree is independent of the
base point and equals the highest homogeneous part evaluated at the
direction. No nonzero-coordinate assumption is made on the direction. -/
theorem linePolynomial_top_coeff (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K) :
    (linePolynomial P a v).coeff P.totalDegree =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  rw [linePolynomial_expansion, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq',
    MvPolynomial.support_homogeneousComponent, Finset.sum_filter]
  simp only [Fin.prod_univ_two, MvPolynomial.coeff_homogeneousComponent]
  apply Finset.sum_congr rfl
  intro s hs
  rw [monomial_line_coeff_of_degree_le _ _ _ _ _ (MvPolynomial.le_totalDegree hs)]
  split_ifs <;> simp_all

theorem linePolynomial_ne_zero (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K)
    (htop : MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0) :
    linePolynomial P a v ≠ 0 := by
  intro hz
  apply htop
  rw [← linePolynomial_top_coeff P a v, hz, Polynomial.coeff_zero]

/-- If the original degree is below the field size and the top component
does not vanish in the chosen direction, every parallel line contains
a point at which the plane polynomial is nonzero. -/
theorem exists_nonzero_on_line [Fintype K]
    (P : MvPolynomial (Fin 2) K) (a v : Fin 2 → K)
    (hdegree : P.totalDegree < Fintype.card K)
    (htop : MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0) :
    ∃ t : K, MvPolynomial.eval (fun i => a i + t * v i) P ≠ 0 := by
  classical
  by_contra hn
  have heval : ∀ t : K, MvPolynomial.eval (fun i => a i + t * v i) P = 0 := by
    simpa only [not_exists, not_not] using hn
  have hzero : linePolynomial P a v = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
    · intro t
      rw [linePolynomial_eval]
      exact heval t
    · exact lt_of_le_of_lt (linePolynomial_degree_le P a v) hdegree
  exact linePolynomial_ne_zero P a v htop hzero

end Cylinder.AffineLinePolynomial
