module

public import Cylinder.PowerSums
public import Cylinder.ProjectionMoments
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Extracting a highest coefficient from projection moments

For a reduced polynomial over the prime field, vanishing mixed moments
through degree `p - 1` force total degree at most `p - 2`.  The moments
themselves are derived from line sums in `ProjectionMoments.lean`.
-/

@[expose] public section

namespace Cylinder.ProjectionDegree

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

abbrev Exponent := Fin 2 →₀ ℕ

def index (a b : ℕ) : Exponent := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem index_zero (a b : ℕ) : index a b 0 = a := by simp [index]
@[simp] theorem index_one (a b : ℕ) : index a b 1 = b := by simp [index]

theorem index_coordinates (m : Exponent) : index (m 0) (m 1) = m := by
  ext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

theorem exponent_degree (m : Exponent) :
    (m.sum fun _ n => n) = m 0 + m 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

variable (p : ℕ) [Fact p.Prime]

def moment (P : MvPolynomial (Fin 2) (ZMod p)) (i j : ℕ) : ZMod p :=
  ∑ x : ZMod p, ∑ y : ZMod p, eval ![x, y] P * x ^ i * y ^ j

theorem eval_monomial_binary (m : Exponent) (c x y : ZMod p) :
    eval ![x, y] (monomial m c) = c * x ^ (m 0) * y ^ (m 1) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]

theorem moment_monomial (m : Exponent) (c : ZMod p) (i j : ℕ) :
    moment p (monomial m c) i j =
      c * (∑ x : ZMod p, x ^ (m 0 + i)) * (∑ y : ZMod p, y ^ (m 1 + j)) := by
  unfold moment
  simp_rw [eval_monomial_binary]
  calc
    (∑ x : ZMod p, ∑ y : ZMod p, c * x ^ m 0 * y ^ m 1 * x ^ i * y ^ j) =
        ∑ x : ZMod p, ∑ y : ZMod p, (c * x ^ (m 0 + i)) * y ^ (m 1 + j) := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      simp only [pow_add]
      ring
    _ = _ := by
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]

theorem moment_sum (s : Finset Exponent)
    (Q : Exponent → MvPolynomial (Fin 2) (ZMod p)) (i j : ℕ) :
    moment p (∑ m ∈ s, Q m) i j = ∑ m ∈ s, moment p (Q m) i j := by
  unfold moment
  simp only [map_sum, sum_mul]
  calc
    (∑ x : ZMod p, ∑ y : ZMod p, ∑ m ∈ s, eval ![x, y] (Q m) * x ^ i * y ^ j) =
        ∑ x : ZMod p, ∑ m ∈ s, ∑ y : ZMod p, eval ![x, y] (Q m) * x ^ i * y ^ j := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = _ := sum_comm

/-- The moment complementary to a maximal monomial extracts exactly its
coefficient. All other monomials have a smaller exponent in some variable. -/
theorem coefficient_extraction (P : MvPolynomial (Fin 2) (ZMod p)) (a b : ℕ)
    (ha : a < p) (hb : b < p) (hdegree : P.totalDegree ≤ a + b) :
    moment p P (p - 1 - a) (p - 1 - b) = P.coeff (index a b) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [moment_sum]
  have hterms (m : Exponent) (hm : m ∈ P.support) :
      moment p (monomial m (P.coeff m)) (p - 1 - a) (p - 1 - b) =
        if m = index a b then P.coeff m else 0 := by
    rw [moment_monomial]
    by_cases heq : m = index a b
    · subst m
      simp only [index_zero, index_one]
      rw [show a + (p - 1 - a) = p - 1 by omega,
        show b + (p - 1 - b) = p - 1 by omega,
        PowerSums.prime_sum_pow_boundary]
      simp
    · rw [ite_eq_right heq]
      have hmdegree : m 0 + m 1 ≤ a + b := by
        rw [← exponent_degree]
        exact (le_totalDegree hm).trans hdegree
      have hsmall : m 0 < a ∨ m 1 < b := by
        by_contra hn
        have hx : a ≤ m 0 := le_of_not_gt (fun h => hn (Or.inl h))
        have hy : b ≤ m 1 := le_of_not_gt (fun h => hn (Or.inr h))
        have hx' : m 0 = a := by omega
        have hy' : m 1 = b := by omega
        apply heq
        rw [← index_coordinates m, hx', hy']
      rcases hsmall with hx | hy
      · rw [PowerSums.prime_sum_pow_low p (m 0 + (p - 1 - a)) (by omega)]
        ring
      · rw [PowerSums.prime_sum_pow_low p (m 1 + (p - 1 - b)) (by omega)]
        ring
  calc
    (∑ m ∈ P.support, moment p (monomial m (P.coeff m)) (p - 1 - a) (p - 1 - b)) =
        ∑ m ∈ P.support, if m = index a b then P.coeff m else 0 := by
      exact sum_congr rfl hterms
    _ = P.coeff (index a b) := by
      by_cases hz : P.coeff (index a b) = 0 <;> simp [mem_support_iff, hz]

/-- The total-degree conclusion in Lemma `lem:projectionpoly`, after the
moment equations have been proved from the geometric line sums. -/
theorem totalDegree_le_of_moments_zero (P : MvPolynomial (Fin 2) (ZMod p))
    (hreduced : ∀ i, P.degreeOf i < p)
    (hmoments : ∀ i j, i + j ≤ p - 1 → moment p P i j = 0) :
    P.totalDegree ≤ p - 2 := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_contra hn
  have hhigh : p - 1 ≤ P.totalDegree := by omega
  have hP : P ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hhigh
    omega
  have hsupport : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨m, hm, hmax⟩ := exists_mem_eq_sup P.support hsupport (fun m => m.sum fun _ n => n)
  have hdegree : P.totalDegree = m 0 + m 1 := hmax.trans (exponent_degree m)
  have ha : m 0 < p := (monomial_le_degreeOf 0 hm).trans_lt (hreduced 0)
  have hb : m 1 < p := (monomial_le_degreeOf 1 hm).trans_lt (hreduced 1)
  have hzero := hmoments (p - 1 - m 0) (p - 1 - m 1) (by omega)
  rw [coefficient_extraction p P (m 0) (m 1) ha hb hdegree.le,
    index_coordinates] at hzero
  exact (mem_support_iff.mp hm) hzero

/-- The degree bound derived directly from geometric line sums. -/
theorem totalDegree_le_of_lineSumsZero (P : MvPolynomial (Fin 2) (ZMod p))
    (hreduced : ∀ i, P.degreeOf i < p)
    (hlines : ProjectionMoments.LineSumsZero p
      (fun z => eval ![z.1, z.2] P)) :
    P.totalDegree ≤ p - 2 := by
  apply totalDegree_le_of_moments_zero p P hreduced
  intro i j hij
  have h := ProjectionMoments.mixed_moment_zero p _ hlines i j hij
  simpa only [moment, Fintype.sum_prod_type] using h

end

end Cylinder.ProjectionDegree
