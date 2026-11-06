module

public import Cylinder.FactorDegreeBound

/-! Distinct prime linear divisors count toward the actual total degree.
This supplies the factor-count step for the missing-direction polynomial. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PrimeLinearFactorCount

variable {K σ I : Type*} [Field K]

theorem prime_linear_factor_count_le_totalDegree (s : Finset I)
    (f : I → MvPolynomial σ K) (P : MvPolynomial σ K) (hP : P ≠ 0)
    (hprime : ∀ i ∈ s, Prime (f i))
    (hsep : (s : Set I).Pairwise (fun i j => ¬Associated (f i) (f j)))
    (hdiv : ∀ i ∈ s, f i ∣ P) (hdegree : ∀ i ∈ s, (f i).totalDegree = 1) :
    s.card ≤ P.totalDegree := by
  apply Cylinder.FactorDegreeBound.linear_factor_count_le_totalDegree s f P hP _ hdiv hdegree
  intro i hi j hj hij
  apply (hprime i hi).irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  exact hsep hi hj hij ((hprime i hi).associated_of_dvd (hprime j hj) h)

theorem eq_zero_of_more_prime_linear_factors (s : Finset I)
    (f : I → MvPolynomial σ K) (P : MvPolynomial σ K)
    (hprime : ∀ i ∈ s, Prime (f i))
    (hsep : (s : Set I).Pairwise (fun i j => ¬Associated (f i) (f j)))
    (hdiv : ∀ i ∈ s, f i ∣ P) (hdegree : ∀ i ∈ s, (f i).totalDegree = 1)
    (hlarge : P.totalDegree < s.card) : P = 0 := by
  by_contra hP
  exact (Nat.not_lt_of_ge (prime_linear_factor_count_le_totalDegree s f P hP hprime hsep hdiv hdegree)) hlarge

end Cylinder.PrimeLinearFactorCount

end
