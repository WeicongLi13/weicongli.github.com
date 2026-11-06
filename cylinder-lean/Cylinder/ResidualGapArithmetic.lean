module

public import Cylinder.DirectionExcess

/-! The strict numerical gap between the actual residual upper and lower bounds. -/

@[expose] public section

namespace Cylinder.ResidualGapArithmetic

theorem actual_residual_gap (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    6 * (1 + p * (p - 1) / 2 - 2 * DirectionExcess.directionLowerBound p) <
      (p - 5) * (p + 1) := by
  let t := DirectionExcess.threshold p
  let n := 1 + p * (p - 1) / 2
  let G := DirectionExcess.directionLowerBound p
  let P : ℚ := p
  let T : ℚ := t
  have htlo : p ≤ 3 * t := by
    dsimp only [t, DirectionExcess.threshold]
    omega
  have hthi : 2 * t ≤ p := by
    dsimp only [t, DirectionExcess.threshold]
    omega
  have ht : t ≤ p := by omega
  have hG : (G : ℚ) = T * (P - T) := by
    dsimp only [G, DirectionExcess.directionLowerBound, T, P, t]
    rw [Nat.cast_mul, Nat.cast_sub ht]
  have hpQ : (11 : ℚ) ≤ P := by dsimp only [P]; exact_mod_cast hp
  have htloQ : P ≤ 3 * T := by dsimp only [P, T]; exact_mod_cast htlo
  have hthiQ : 2 * T ≤ P := by dsimp only [P, T]; exact_mod_cast hthi
  have hprod : 0 ≤ (3 * T - P) * (2 * P - 3 * T) :=
    mul_nonneg (by linarith only [htloQ]) (by linarith only [hthiQ, hpQ])
  have hGlo : 2 * P ^ 2 ≤ 9 * (G : ℚ) := by
    rw [hG]
    nlinarith only [hprod]
  have hnNat : 2 * n ≤ 2 + p * (p - 1) := by
    dsimp only [n]
    have hdiv := Nat.div_mul_le_self (p * (p - 1)) 2
    omega
  have hp1 : 1 ≤ p := by omega
  have hnQ : 2 * (n : ℚ) ≤ 2 + P * (P - 1) := by
    have hh : 2 * (n : ℚ) ≤ 2 + (p : ℚ) * ((p - 1 : ℕ) : ℚ) := by
      exact_mod_cast hnNat
    simpa only [Nat.cast_sub hp1, Nat.cast_one, P] using hh
  have hpos : 0 < 2 * P ^ 2 - 3 * P - 33 := by
    have hsquare := sq_nonneg (P - 11)
    nlinarith only [hpQ, hsquare]
  have hgapQ : 6 * (n : ℚ) < (P - 5) * (P + 1) + 12 * (G : ℚ) := by
    nlinarith only [hnQ, hGlo, hpos]
  have hp5 : 5 ≤ p := by omega
  have hgap : 6 * n < (p - 5) * (p + 1) + 12 * G := by
    have hh : 6 * (n : ℚ) < ((p - 5 : ℕ) : ℚ) * ((p + 1 : ℕ) : ℚ) + 12 * (G : ℚ) := by
      simpa only [Nat.cast_sub hp5, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, P] using hgapQ
    exact_mod_cast hh
  have hpositive : 0 < (p - 5) * (p + 1) := Nat.mul_pos (by omega) (by omega)
  change 6 * (n - 2 * G) < (p - 5) * (p + 1)
  omega

theorem actual_residual_bounds_inconsistent (p N : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (hlower : (p - 5) * (p + 1) ≤ 2 * N)
    (hupper : 2 * N ≤
      6 * (1 + p * (p - 1) / 2 - 2 * DirectionExcess.directionLowerBound p)) : False := by
  have hgap := actual_residual_gap p hp
  omega

end Cylinder.ResidualGapArithmetic

end
