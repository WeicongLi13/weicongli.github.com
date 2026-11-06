module

public import Cylinder.ExactRayMomentsSeparation
public import Mathlib.Algebra.Prime.Lemmas

/-!
# An actual pole forces the corresponding highest moment to be nonzero

Vanishing of one coefficient makes the remaining rational sum regular at
that actual prime. Clearing its denominator contradicts the actual numerator
and denominator prime-power divisibilities. These divisibility data must
still be derived from the black and white product multiplicities to obtain
the full geometric exact-moments proposition.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsHighest
open Cylinder.ExactRayMomentsSeparation
variable {K R F I : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Field F] [Algebra R F] [IsFractionRing R F] [Fintype I]

theorem fraction_sum_regular_of_coefficient_zero (a : I → R) (ha : ∀ i, Prime (a i))
    (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k) (m : I → K) (n : ℕ) (i : I) (hmi : m i = 0) :
    ∃ D Q : R, (¬a i ∣ D) ∧ D ≠ 0 ∧
      (∑ k, algebraMap R F (algebraMap K R (m k)) / algebraMap R F (a k) ^ n) =
        algebraMap R F Q / algebraMap R F D := by
  let J := {k : I // k ≠ i}
  let a' : J → R := fun k => a k.val
  let m' : J → K := fun k => m k.val
  let D := ∏ k : J, a' k ^ n
  let Q := cofactorSum a' m' n
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun k _ => pow_ne_zero n (ha k.val).ne_zero)
  have hnot : ¬a i ∣ D := by
    intro hd
    obtain ⟨k, _, hk⟩ := ((ha i).dvd_finsetProd_iff (fun k : J => a' k ^ n)).mp hd
    exact hsep i k.val (Ne.symm k.property) ((ha i).dvd_of_dvd_pow hk)
  have hDmap : algebraMap R F D ≠ 0 := by
    intro hz
    exact hD0 (IsFractionRing.injective R F (by simpa using hz))
  have hclear := fraction_sum_cleared (F := F) a' (fun k => (ha k.val).ne_zero) m' n
  have hrest : (∑ k : J, algebraMap R F (algebraMap K R (m k.val)) /
      algebraMap R F (a k.val) ^ n) = algebraMap R F Q / algebraMap R F D :=
    (eq_div_iff hDmap).mpr hclear.symm
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun k : I => k ≠ i)
    (fun k => algebraMap R F (algebraMap K R (m k)) / algebraMap R F (a k) ^ n)
  have hcomp : (∑ k : {k : I // ¬k ≠ i}, algebraMap R F (algebraMap K R (m k.val)) /
      algebraMap R F (a k.val) ^ n) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val = i := not_not.mp k.property
    simp only [hk, hmi, map_zero, zero_div]
  rw [hcomp, add_zero] at hsplit
  exact ⟨D, Q, hnot, hD0, hsplit.symm.trans hrest⟩

theorem actual_poles_force_coefficients_nonzero
    (a : I → R) (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (m : I → K) (n : ℕ) (A B u : R) (hB0 : B ≠ 0) (q : I → ℕ)
    (hden : ∀ i, a i ^ q i ∣ B) (hnum : ∀ i, ¬a i ^ q i ∣ A)
    (hquot : algebraMap R F A / algebraMap R F B = algebraMap R F u *
      ∑ i, algebraMap R F (algebraMap K R (m i)) / algebraMap R F (a i) ^ n) :
    ∀ i, m i ≠ 0 := by
  intro i hmi
  obtain ⟨D, Q, hnot, hD0, hregular⟩ :=
    fraction_sum_regular_of_coefficient_zero (F := F) a ha hsep m n i hmi
  have hBmap : algebraMap R F B ≠ 0 := by
    intro hz
    exact hB0 (IsFractionRing.injective R F (by simpa using hz))
  have hDmap : algebraMap R F D ≠ 0 := by
    intro hz
    exact hD0 (IsFractionRing.injective R F (by simpa using hz))
  rw [hregular, ← mul_div_assoc, ← map_mul] at hquot
  have heq := (div_eq_div_iff hBmap hDmap).mp hquot
  have heqR : A * D = (u * Q) * B := by
    apply IsFractionRing.injective R F
    simpa only [map_mul] using heq
  have hdiv : a i ^ q i ∣ A * D := by
    rw [heqR]
    exact dvd_mul_of_dvd_right (hden i) _
  exact hnum i ((ha i).pow_dvd_of_dvd_mul_right (q i) hnot hdiv)

end Cylinder.ExactRayMomentsHighest
end
