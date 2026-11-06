module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Counting distinct linear factors by total degree

Pairwise relatively prime degree-one divisors of a nonzero multivariate
polynomial have a product dividing that polynomial. Total degree is
additive in a domain, so their number is at most its total degree.
The geometric identification of distinct empty lines with such factors
is proved separately in the line modules.
-/

@[expose] public section

noncomputable section

namespace Cylinder.FactorDegreeBound

open MvPolynomial
open scoped BigOperators Classical

variable {K σ ι : Type*} [Field K]

theorem totalDegree_prod (s : Finset ι) (f : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        totalDegree_mul_of_isDomain (hf a (Finset.mem_insert_self _ _))
          (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem linear_factor_count_le_totalDegree (s : Finset ι)
    (f : ι → MvPolynomial σ K) (P : MvPolynomial σ K) (hP : P ≠ 0)
    (hrel : (s : Set ι).Pairwise (fun i j => IsRelPrime (f i) (f j)))
    (hdiv : ∀ i ∈ s, f i ∣ P)
    (hdegree : ∀ i ∈ s, (f i).totalDegree = 1) :
    s.card ≤ P.totalDegree := by
  have hf : ∀ i ∈ s, f i ≠ 0 := by
    intro i hi hz
    have h := hdegree i hi
    rw [hz, totalDegree_zero] at h
    exact Nat.zero_ne_one h
  have hprod : (∏ i ∈ s, f i) ∣ P := Finset.prod_dvd_of_isRelPrime hrel hdiv
  have hle := totalDegree_le_of_dvd_of_isDomain hprod hP
  rw [totalDegree_prod s f hf] at hle
  simpa only [Finset.sum_const_nat (fun i hi => hdegree i hi), mul_one] using hle

end Cylinder.FactorDegreeBound

end
