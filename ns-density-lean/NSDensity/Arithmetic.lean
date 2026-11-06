import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Elementary arithmetic for the construction operations. No external assumptions. -/

namespace NSDensity

/-- A useful division form of the least common multiple. -/
theorem lcm_eq_mul_div_gcd (n A : ℕ) :
    Nat.lcm n A = n * (A / Nat.gcd n A) := by
  rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc _ (Nat.gcd_dvd_right n A)]

/-- The extension condition is exactly divisibility by the scalar lcm. -/
theorem extension_iff_mul_dvd_lcm {n A u : ℕ} (hn : 0 < n) :
    u ∣ A / Nat.gcd n A ↔ n * u ∣ Nat.lcm n A := by
  rw [lcm_eq_mul_div_gcd, Nat.mul_dvd_mul_iff_left hn]

/-- Enlarging the scalar alphabet enlarges the permitted extension quotient. -/
theorem div_gcd_dvd_div_gcd {n A B : ℕ} (hn : 0 < n) (hAB : A ∣ B) :
    A / Nat.gcd n A ∣ B / Nat.gcd n B := by
  rw [← Nat.mul_dvd_mul_iff_left hn, ← lcm_eq_mul_div_gcd,
    ← lcm_eq_mul_div_gcd]
  exact Nat.lcm_dvd (Nat.dvd_lcm_left n B)
    (dvd_trans hAB (Nat.dvd_lcm_right n B))

/-- The scalar intersection grows by precisely the extension factor. -/
theorem gcd_extension {n A u : ℕ} (hn : 0 < n)
    (hu : u ∣ A / Nat.gcd n A) :
    Nat.gcd (n * u) A = u * Nat.gcd n A := by
  let e := Nat.gcd n A
  have he : 0 < e := Nat.gcd_pos_of_pos_left A hn
  have hcop : (n / e).Coprime (A / e) := Nat.coprime_div_gcd_div_gcd he
  have hne : e * (n / e) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n A)
  have hAe : e * (A / e) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_right n A)
  calc
    Nat.gcd (n * u) A = Nat.gcd (e * ((n / e) * u)) (e * (A / e)) := by
      rw [← mul_assoc, hne, hAe]
    _ = e * Nat.gcd ((n / e) * u) (A / e) := Nat.gcd_mul_left _ _ _
    _ = e * u := by rw [Nat.gcd_mul_of_coprime_of_dvd hcop hu]
    _ = u * Nat.gcd n A := Nat.mul_comm _ _

/-- Reduction of the modulus can only decrease the multiplicative order by divisibility. -/
theorem order_dvd_of_modulus_dvd {d n q : ℕ} (hdn : d ∣ n) :
    orderOf (q : ZMod d) ∣ orderOf (q : ZMod n) := by
  simpa using orderOf_map_dvd (ZMod.castHom hdn (ZMod d)).toMonoidHom (q : ZMod n)
/-- Multiplication by an admissible extension factor preserves multiplicative order. -/
theorem order_extension {n q u : ℕ} (hn : 0 < n) (hq : 1 ≤ q)
    (hu : u ∣ (q - 1) / Nat.gcd n (q - 1)) :
    orderOf (q : ZMod (n * u)) = orderOf (q : ZMod n) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    let m := orderOf (q : ZMod n)
    have hqpow : 1 ≤ q ^ m := one_le_pow₀ hq
    have hnmod : 1 ≡ q ^ m [MOD n] := by
      apply (ZMod.natCast_eq_natCast_iff 1 (q ^ m) n).mp
      simpa only [Nat.cast_one, Nat.cast_pow] using (pow_orderOf_eq_one (q : ZMod n)).symm
    have hnsub : n ∣ q ^ m - 1 := (Nat.modEq_iff_dvd' hqpow).mp hnmod
    have hqmod : 1 ≡ q [MOD q - 1] := (Nat.modEq_iff_dvd' hq).mpr (dvd_refl _)
    have hqsub : q - 1 ∣ q ^ m - 1 := by
      apply (Nat.modEq_iff_dvd' hqpow).mp
      simpa only [one_pow] using hqmod.pow m
    have hnum : n * u ∣ q ^ m - 1 := dvd_trans
      ((extension_iff_mul_dvd_lcm hn).mp hu) (Nat.lcm_dvd hnsub hqsub)
    have hnumod : 1 ≡ q ^ m [MOD n * u] := (Nat.modEq_iff_dvd' hqpow).mpr hnum
    have hcast := (ZMod.natCast_eq_natCast_iff 1 (q ^ m) (n * u)).mpr hnumod
    simpa only [Nat.cast_one, Nat.cast_pow] using hcast.symm
  · exact order_dvd_of_modulus_dvd (Nat.dvd_mul_right n u)

/-- For a positive modulus, a coprime base has positive multiplicative order. -/
theorem order_pos {n q : ℕ} (hn : 0 < n) (hcop : Nat.Coprime q n) :
    0 < orderOf (q : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact ((ZMod.isUnit_iff_coprime q n).mpr hcop).isOfFinOrder.orderOf_pos

/-- The multiplicative order of a positive power of the base. -/
theorem order_power {n q t : ℕ} (ht : 0 < t) :
    orderOf (q ^ t : ZMod n) =
      orderOf (q : ZMod n) / Nat.gcd (orderOf (q : ZMod n)) t := by
  simpa only [Nat.cast_pow] using
    orderOf_pow' (x := (q : ZMod n)) (Nat.ne_of_gt ht)

/-- An admissible lift preserves the multiplicative order. -/
theorem order_lift {n q t : ℕ} (hcop : Nat.Coprime t (orderOf (q : ZMod n))) :
    orderOf (q ^ t : ZMod n) = orderOf (q : ZMod n) := by
  simpa only [Nat.cast_pow] using hcop.symm.orderOf_pow (y := (q : ZMod n))

/-- If a modulus divides a power minus one, its order divides the exponent. -/
theorem order_dvd_of_dvd_pow_sub_one {n q t : ℕ} (hq : 1 ≤ q)
    (h : n ∣ q ^ t - 1) : orderOf (q : ZMod n) ∣ t := by
  apply orderOf_dvd_of_pow_eq_one
  have hmod : 1 ≡ q ^ t [MOD n] := (Nat.modEq_iff_dvd' (one_le_pow₀ hq)).mpr h
  have hcast := (ZMod.natCast_eq_natCast_iff 1 (q ^ t) n).mpr hmod
  simpa only [Nat.cast_one, Nat.cast_pow] using hcast.symm

/-- A base minus one divides every power of that base minus one. -/
theorem sub_one_dvd_pow_sub_one {q t : ℕ} (hq : 1 ≤ q) : q - 1 ∣ q ^ t - 1 := by
  apply (Nat.modEq_iff_dvd' (one_le_pow₀ hq)).mp
  have hmod : 1 ≡ q [MOD q - 1] := (Nat.modEq_iff_dvd' hq).mpr (dvd_refl _)
  simpa only [one_pow] using hmod.pow t

end NSDensity
