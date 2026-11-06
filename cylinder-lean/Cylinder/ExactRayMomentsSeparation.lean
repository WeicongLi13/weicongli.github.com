module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Separation of poles at actual different prime factors

A sum of scalar coefficients over positive powers of pairwise different
prime elements can vanish only when every scalar coefficient vanishes. The
proof clears the actual denominator and uses divisibility in the domain.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsSeparation
variable {K R I : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Fintype I]

def cofactorSum (a : I → R) (m : I → K) (n : ℕ) : R :=
  ∑ i, algebraMap K R (m i) * ∏ j ∈ Finset.univ.erase i, a j ^ n

omit [IsDomain R] in
theorem prime_cofactor_sum_zero (a : I → R) (ha : ∀ i, Prime (a i))
    (hsep : ∀ i j, i ≠ j → ¬a i ∣ a j) (m : I → K) (n : ℕ) (hn : 0 < n)
    (hsum : cofactorSum a m n = 0) : ∀ i, m i = 0 := by
  intro i
  let term (j : I) := algebraMap K R (m j) * ∏ k ∈ Finset.univ.erase j, a k ^ n
  have hsum' : ∑ j, term j = 0 := hsum
  have hother : a i ∣ ∑ j ∈ Finset.univ.erase i, term j := by
    apply Finset.dvd_sum
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hik : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ _⟩
    apply dvd_mul_of_dvd_right
    apply (dvd_pow_self (a i) (by omega : n ≠ 0)).trans
    exact Finset.dvd_prod_of_mem _ hik
  have heq : term i + (∑ j ∈ Finset.univ.erase i, term j) = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact hsum'
  have hterm : a i ∣ term i := by
    rw [eq_neg_of_add_eq_zero_left heq]
    exact dvd_neg.mpr hother
  have hnot : ¬a i ∣ ∏ j ∈ Finset.univ.erase i, a j ^ n := by
    intro h
    obtain ⟨j, hj, hd⟩ := ((ha i).dvd_finsetProd_iff (fun j => a j ^ n)).mp h
    exact hsep i j (Ne.symm (Finset.mem_erase.mp hj).1)
      (((ha i).dvd_pow_iff_dvd (by omega)).mp hd)
  have hscalar : a i ∣ algebraMap K R (m i) :=
    ((ha i).dvd_mul.mp hterm).resolve_right hnot
  by_contra hmi
  have hu : IsUnit (algebraMap K R (m i)) :=
    (isUnit_iff_ne_zero.mpr hmi).map (algebraMap K R)
  exact (ha i).not_isUnit (isUnit_of_dvd_unit hscalar hu)

variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

theorem fraction_sum_cleared (a : I → R) (ha : ∀ i, a i ≠ 0) (m : I → K) (n : ℕ) :
    algebraMap R F (cofactorSum a m n) =
      (∑ i, algebraMap R F (algebraMap K R (m i)) / algebraMap R F (a i) ^ n) *
        algebraMap R F (∏ i, a i ^ n) := by
  rw [cofactorSum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hf : (∏ j, a j ^ n) = a i ^ n * ∏ j ∈ Finset.univ.erase i, a j ^ n :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have haF : algebraMap R F (a i) ≠ 0 := by
    intro h
    exact ha i ((IsFractionRing.injective R F) (by simpa using h))
  rw [hf]
  simp only [map_mul, map_pow]
  field_simp [haF]

theorem prime_fraction_sum_zero (a : I → R) (ha : ∀ i, Prime (a i))
    (hsep : ∀ i j, i ≠ j → ¬a i ∣ a j) (m : I → K) (n : ℕ) (hn : 0 < n)
    (hsum : (∑ i, algebraMap R F (algebraMap K R (m i)) / algebraMap R F (a i) ^ n) = 0) :
    ∀ i, m i = 0 := by
  apply prime_cofactor_sum_zero a ha hsep m n hn
  apply IsFractionRing.injective R F
  rw [fraction_sum_cleared a (fun i => (ha i).ne_zero), hsum, zero_mul, map_zero]

end Cylinder.ExactRayMomentsSeparation
end
