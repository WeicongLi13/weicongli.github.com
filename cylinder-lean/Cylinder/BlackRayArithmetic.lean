module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Rat.Cast.Order

/-!
# The numerical contradictions in the black-point ray argument

All rounding bounds use the actual natural-number quotient expressions.
The cubic comparison is proved from its polynomial chord identity over the
rationals, rather than assumed as a concavity or lower-bound hypothesis.
-/

@[expose] public section
namespace Cylinder.BlackRayArithmetic

def rayCeiling (p r : ℕ) : ℕ := (p - 2 * r + 7) / 3

theorem rayCeiling_bounds (p r : ℕ) :
    p - 2 * r + 5 ≤ 3 * rayCeiling p r ∧
      3 * rayCeiling p r ≤ p - 2 * r + 7 := by
  unfold rayCeiling
  omega

theorem rayCeiling_le_of_not_small (p r s : ℕ) (h : p - 2 * r + 5 ≤ 3 * s) :
    rayCeiling p r ≤ s := by
  unfold rayCeiling
  omega

theorem small_degree_lt_prime (p r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hsmall : 3 * s < p - 2 * r + 5) : s < p := by
  omega

private def cubic (P R : ℚ) : ℚ := R * (P - 2 * R + 5) * (2 * P - R + 1)

private theorem cubic_chord_strict (P R : ℚ) (hp : 7 ≤ P) (hr : 3 ≤ R)
    (hrp : 2 * R ≤ P - 1) : 9 * (1 + P * (P - 1) / 2) < cubic P R := by
  let H : ℚ := (P - 1) / 2
  let U : ℚ := 9 * (1 + P * (P - 1) / 2)
  have hRH : R ≤ H := by dsimp [H]; linarith
  have hH3 : 3 ≤ H := by dsimp [H]; linarith
  have hF3 : U + 18 ≤ cubic P 3 := by
    have hprod : 0 ≤ (P - 7) * (P + 2) := mul_nonneg (by linarith) (by linarith)
    dsimp [U, cubic]
    nlinarith
  have hFH : U + 18 ≤ cubic P H := by
    dsimp [U, cubic, H]
    nlinarith
  by_cases hH : H = 3
  · have hR : R = 3 := by linarith
    rw [hR]
    dsimp [U] at hF3
    linarith
  have hHgt : 3 < H := lt_of_le_of_ne hH3 (Ne.symm hH)
  have hHpos : 0 < H - 3 := by linarith
  have hweight0 : 0 ≤ H - R := by linarith
  have hweight1 : 0 ≤ R - 3 := by linarith
  have hlast : 0 ≤ 2 * P + 1 - R := by linarith
  have hdefect : 0 ≤ 2 * (R - 3) * (H - R) * (2 * P + 1 - R) * (H - 3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hweight1) hweight0) hlast)
      (le_of_lt hHpos)
  have hid : (H - 3) * cubic P R -
      ((H - R) * cubic P 3 + (R - 3) * cubic P H) =
      2 * (R - 3) * (H - R) * (2 * P + 1 - R) * (H - 3) := by
    dsimp [H, cubic]
    ring
  have hw0 := mul_nonneg hweight0 (sub_nonneg.mpr hF3)
  have hw1 := mul_nonneg hweight1 (sub_nonneg.mpr hFH)
  change U < cubic P R
  by_contra hn
  have hbad := mul_nonneg (le_of_lt hHpos) (sub_nonneg.mpr (le_of_not_gt hn))
  nlinarith

theorem ray_ceiling_contradiction (p r n : ℕ) (hp : 7 ≤ p) (hr : 3 ≤ r)
    (hrp : r ≤ (p - 1) / 2) (hn : n ≤ 1 + p * (p - 1) / 2)
    (hlower : r * rayCeiling p r * (p - r + 2 - rayCeiling p r) ≤ n) : False := by
  let P : ℚ := p
  let R : ℚ := r
  let T : ℚ := rayCeiling p r
  have h2r : 2 * r ≤ p := by omega
  have hrle : r ≤ p := by omega
  have hp1 : 1 ≤ p := by omega
  obtain ⟨htlo, hthi⟩ := rayCeiling_bounds p r
  have htA : rayCeiling p r ≤ p - r + 2 := by omega
  have hPQ : (7 : ℚ) ≤ P := by dsimp [P]; exact_mod_cast hp
  have hRQ : (3 : ℚ) ≤ R := by dsimp [R]; exact_mod_cast hr
  have h2RQ : 2 * R ≤ P - 1 := by
    have hh : 2 * r + 1 ≤ p := by omega
    have hhQ : 2 * R + 1 ≤ P := by dsimp [P, R]; exact_mod_cast hh
    linarith
  have htloQ : P - 2 * R + 5 ≤ 3 * T := by
    dsimp [P, R, T]
    have h : ((p - 2 * r + 5 : ℕ) : ℚ) ≤ 3 * (rayCeiling p r : ℚ) := by exact_mod_cast htlo
    simpa only [Nat.cast_add, Nat.cast_sub h2r, Nat.cast_mul, Nat.cast_ofNat] using h
  have hthiQ : 3 * T ≤ P - 2 * R + 7 := by
    dsimp [P, R, T]
    have h : 3 * (rayCeiling p r : ℚ) ≤ ((p - 2 * r + 7 : ℕ) : ℚ) := by exact_mod_cast hthi
    simpa only [Nat.cast_add, Nat.cast_sub h2r, Nat.cast_mul, Nat.cast_ofNat] using h
  let X : ℚ := (P - 2 * R + 5) / 3
  let A : ℚ := P - R + 2
  have hTX : 0 ≤ T - X := by dsimp [X]; linarith
  have hATX : 0 ≤ A - T - X := by dsimp [A, X]; linarith
  have hprod := mul_nonneg (show 0 ≤ R by linarith) (mul_nonneg hTX hATX)
  have hid : R * T * (A - T) - cubic P R / 9 = R * ((T - X) * (A - T - X)) := by
    dsimp [A, X, cubic]
    ring
  have hpoly : cubic P R / 9 ≤ R * T * (A - T) := by nlinarith
  have hnQ : (n : ℚ) ≤ 1 + P * (P - 1) / 2 := by
    have hnd : (n : ℚ) ≤ 1 + ((p * (p - 1) / 2 : ℕ) : ℚ) := by exact_mod_cast hn
    have hdiv := Nat.div_mul_le_self (p * (p - 1)) 2
    have hdivQ : ((p * (p - 1) / 2 : ℕ) : ℚ) * 2 ≤ P * (P - 1) := by
      have hh : ((p * (p - 1) / 2 : ℕ) : ℚ) * 2 ≤ ((p * (p - 1) : ℕ) : ℚ) := by
        exact_mod_cast hdiv
      simpa only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one] using hh
    linarith
  have hlowerQ : R * T * (A - T) ≤ (n : ℚ) := by
    have hh : ((r * rayCeiling p r * (p - r + 2 - rayCeiling p r) : ℕ) : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast hlower
    simpa only [Nat.cast_mul, Nat.cast_sub htA, Nat.cast_add, Nat.cast_sub hrle, Nat.cast_ofNat]
      using hh
  have hcubic := cubic_chord_strict P R hPQ hRQ h2RQ
  linarith

theorem line_bound_strict (p r : ℕ) (hr : 2 ≤ r) (hrp : r ≤ (p - 1) / 2) :
    (p - 1) / r < p - r + 1 := by
  have hp : 1 ≤ p := by omega
  have hpr : r ≤ p := by omega
  have hstrict : p - 1 < 2 * (p - r + 1) := by omega
  have hprod := Nat.mul_le_mul_right (p - r + 1) hr
  by_contra hn
  have hm := Nat.mul_le_mul_right r (le_of_not_gt hn)
  have hdiv := Nat.div_mul_le_self (p - 1) r
  nlinarith

theorem small_degree_polar_strict (p r s : ℕ) (hs : 2 ≤ s)
    (hsmall : 3 * s < p - 2 * r + 5) :
    s * (s + p - 1) < 2 * s * (p - r + 2 - s) := by
  have hab : s + p - 1 < 2 * (p - r + 2 - s) := by omega
  have h := Nat.mul_lt_mul_of_pos_left hab (show 0 < s by omega)
  nlinarith

end Cylinder.BlackRayArithmetic
end
