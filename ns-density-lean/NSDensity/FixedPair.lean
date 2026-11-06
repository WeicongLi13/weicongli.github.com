import NSDensity.Inputs
import NSDensity.Tails

namespace NSDensity

/-- Multipliers permitted by a single lift and extension from (a,b). -/
def AdmissibleMultipliers (a b : ℕ) : Set ℕ :=
  {u | ∃ t : ℕ, 0 < t ∧ Nat.Coprime t (orderOf (b : ZMod a)) ∧
    u ∣ (b ^ t - 1) / Nat.gcd a (b ^ t - 1)}

theorem admissible_order_dvd {a b u t : ℕ} (hb : 1 ≤ b)
    (hu : u ∣ (b ^ t - 1) / Nat.gcd a (b ^ t - 1)) :
    orderOf (b : ZMod u) ∣ t := by
  apply order_dvd_of_dvd_pow_sub_one hb
  exact dvd_trans hu (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a (b ^ t - 1)))

theorem admissible_avoids {a b ℓ : ℕ} (hb : 1 ≤ b) (hℓ : ℓ.Prime)
    (hℓm : ℓ ∣ orderOf (b : ZMod a)) :
    AdmissibleMultipliers a b ⊆ avoids (OrderPrimes b ℓ) := by
  intro u hu r hr hru
  obtain ⟨t, ht, hcop, hu⟩ := hu
  have hℓt : ℓ ∣ t := dvd_trans hr.2.2
    (dvd_trans (order_dvd_of_modulus_dvd hru) (admissible_order_dvd hb hu))
  have hℓgcd : ℓ ∣ Nat.gcd t (orderOf (b : ZMod a)) := Nat.dvd_gcd hℓt hℓm
  rw [hcop.gcd_eq_one] at hℓgcd
  exact hℓ.not_dvd_one hℓgcd

theorem densityZero_admissibleMultipliers (hWM : WiertelakMoreeInput)
    {a b : ℕ} (hb : 1 < b) (hm : 1 < orderOf (b : ZMod a)) :
    DensityZero (AdmissibleMultipliers a b) := by
  obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd (by omega : orderOf (b : ZMod a) ≠ 1)
  exact (densityZero_avoids_orderPrimes hWM hb hℓ.one_lt).mono
    (admissible_avoids hb.le hℓ hℓm)

def NormalLengths (a b : ℕ) : Set ℕ := scaled a (AdmissibleMultipliers a b)

theorem densityZero_normalLengths (hWM : WiertelakMoreeInput)
    {a b : ℕ} (ha : 0 < a) (hb : 1 < b) (hm : 1 < orderOf (b : ZMod a)) :
    DensityZero (NormalLengths a b) :=
  (densityZero_admissibleMultipliers hWM hb hm).scaled a ha

theorem normalLengths_subset_multiples (a b : ℕ) :
    NormalLengths a b ⊆ {n : ℕ | a ∣ n} := by
  rintro n ⟨u, _, rfl⟩
  exact Nat.dvd_mul_right a u

/-- A divisor of a power minus one, larger than b-1, has degree greater than one. -/
theorem order_gt_one_of_large_divisor {a b k : ℕ} (hb : 1 < b) (hk : 0 < k)
    (hdiv : a ∣ b ^ k - 1) (hlarge : b - 1 < a) :
    1 < orderOf (b : ZMod a) := by
  have hd := order_dvd_of_dvd_pow_sub_one hb.le hdiv
  have hne0 : orderOf (b : ZMod a) ≠ 0 := by
    intro h
    rw [h] at hd
    simp only [zero_dvd_iff] at hd
    omega
  have hne1 : orderOf (b : ZMod a) ≠ 1 := by
    intro h
    have hcast : (b : ZMod a) = 1 := by
      simpa only [h, pow_one] using pow_orderOf_eq_one (b : ZMod a)
    have hmod : 1 ≡ b [MOD a] := by
      apply (ZMod.natCast_eq_natCast_iff 1 b a).mp
      simpa only [Nat.cast_one] using hcast.symm
    have hsub : a ∣ b - 1 := (Nat.modEq_iff_dvd' hb.le).mp hmod
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hb) hsub
    omega
  omega

def DualRepetitionLengths (p : ℕ) : Set ℕ :=
  {n | ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf (p : ZMod r) = r - 1 ∧
    n ∈ NormalLengths r p}

theorem dualRepetitionLengths_subset (p : ℕ) (hp : 1 < p) :
    DualRepetitionLengths p ⊆ atMostOne (OrderPrimes p 2) := by
  rintro n ⟨r, hr, hr5, hrord, u, ⟨t, ht, hcop, hu⟩, hnu⟩
  have hrmod : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
  have h2m : 2 ∣ orderOf (p : ZMod r) := by
    rw [hrord, Nat.dvd_iff_mod_eq_zero]
    omega
  have havoid : ∀ s ∈ OrderPrimes p 2, ¬s ∣ u := by
    intro s hs hsu
    have h2t : 2 ∣ t := dvd_trans hs.2.2
      (dvd_trans (order_dvd_of_modulus_dvd hsu) (admissible_order_dvd hp.le hu))
    have h2gcd := Nat.dvd_gcd h2t h2m
    rw [hcop.gcd_eq_one] at h2gcd
    norm_num at h2gcd
  have heq : ∀ s ∈ OrderPrimes p 2, s ∣ n → s = r := by
    intro s hs hsn
    rw [hnu] at hsn
    rcases hs.1.dvd_mul.mp hsn with hsr | hsu
    · exact (Nat.prime_dvd_prime_iff_eq hs.1 hr).mp hsr
    · exact False.elim (havoid s hs hsu)
  intro s hs v hv hsn hvn
  exact (heq s hs hsn).trans (heq v hv hvn).symm

theorem densityZero_dualRepetitionLengths (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : 1 < p) : DensityZero (DualRepetitionLengths p) :=
  (densityZero_atMostOne_orderPrimes hWM hp (by decide : 1 < 2)).mono
    (dualRepetitionLengths_subset p hp)

end NSDensity
