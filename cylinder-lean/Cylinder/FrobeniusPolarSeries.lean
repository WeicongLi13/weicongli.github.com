module

public import Cylinder.FrobeniusPolarDifferential
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Vanishing coefficients after the second formal derivative

In characteristic `p`, a power series with zero second derivative has
no coefficients in degrees `2,...,p-1`. Consequently its difference
from its linear truncation is divisible by `X^p` and has order at least
`p`. These are statements about actual formal power series. An
identification of this order with a curve's local intersection number
is not asserted here.
-/

@[expose] public section

noncomputable section

namespace Cylinder.FrobeniusPolarSeries

open PowerSeries
open scoped Classical

variable {K : Type*} [Field K]
variable (p : ℕ) [CharP K p]

theorem natCast_ne_zero_of_pos_lt (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (j : K) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff K p j).mp hz
  have hjzero := Nat.eq_zero_of_dvd_of_lt hd hjp
  omega

theorem coeff_eq_zero_of_second_derivative (f : K⟦X⟧)
    (hsecond : derivative (derivative f) = 0) (j : ℕ) (hj : 2 ≤ j) (hjp : j < p) :
    coeff j f = 0 := by
  have h := congrArg (coeff (j - 2)) hsecond
  simp only [coeff_derivative, map_zero] at h
  have hindex : j - 1 + 1 = j := by omega
  have hindex' : j - 2 + 1 = j - 1 := by omega
  have hcast : ((j - 1 : ℕ) : K) + 1 = (j : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) hindex
  have hcast' : ((j - 2 : ℕ) : K) + 1 = ((j - 1 : ℕ) : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) hindex'
  have h' : coeff j f * (j : K) * ((j - 1 : ℕ) : K) = 0 := by
    simpa only [hindex', hindex, hcast', hcast] using h
  have hjcast := natCast_ne_zero_of_pos_lt (K := K) p j (by omega) hjp
  have hjcast' := natCast_ne_zero_of_pos_lt (K := K) p (j - 1) (by omega) (by omega)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hjcast')).resolve_right hjcast

def linearTruncation (f : K⟦X⟧) : K⟦X⟧ :=
  C (coeff 0 f) + C (coeff 1 f) * X

theorem coeff_sub_linearTruncation_below_char (f : K⟦X⟧)
    (hsecond : derivative (derivative f) = 0) (j : ℕ) (hjp : j < p) :
    coeff j (f - linearTruncation f) = 0 := by
  by_cases hj0 : j = 0
  · subst j
    simp [linearTruncation]
  by_cases hj1 : j = 1
  · subst j
    simp [linearTruncation, coeff_C]
  have hj : 2 ≤ j := by omega
  simp [linearTruncation, coeff_C, coeff_C_mul, coeff_X, hj0, hj1,
    coeff_eq_zero_of_second_derivative p f hsecond j hj hjp]

theorem X_pow_dvd_sub_linearTruncation (f : K⟦X⟧)
    (hsecond : derivative (derivative f) = 0) :
    (X : K⟦X⟧) ^ p ∣ f - linearTruncation f := by
  rw [X_pow_dvd_iff]
  exact coeff_sub_linearTruncation_below_char p f hsecond

theorem order_sub_linearTruncation_ge_char (f : K⟦X⟧)
    (hsecond : derivative (derivative f) = 0) :
    (p : ℕ∞) ≤ order (f - linearTruncation f) := by
  rw [nat_le_order_iff]
  exact coeff_sub_linearTruncation_below_char p f hsecond

end Cylinder.FrobeniusPolarSeries

end
