module

public import Cylinder.BlackRayArithmetic

/-! The complete strict-threshold calculation for the residual-point bound. -/

@[expose] public section

namespace Cylinder.ResidualRayArithmetic

def residualThreshold (p r : ℕ) : ℕ := max 2 ((p - 2 * r + 3) / 3)

theorem threshold_space (p r : ℕ) (hp : 11 ≤ p) (hr : 3 ≤ r) (hhalf : r ≤ (p - 1) / 2) :
    2 * residualThreshold p r ≤ p - r := by
  unfold residualThreshold
  omega

theorem residual_ray_lower_bound (p r N : ℕ)
    (hp : 11 ≤ p) (hr : 3 ≤ r) (hhalf : r ≤ (p - 1) / 2)
    (hlower : r * residualThreshold p r * (p - r - residualThreshold p r) ≤ N) :
    (p - 5) * (p + 1) ≤ 2 * N := by
  let t := residualThreshold p r
  let P : ℚ := p
  let R : ℚ := r
  let T : ℚ := t
  change r * t * (p - r - t) ≤ N at hlower
  have hspace : 2 * t ≤ p - r := threshold_space p r hp hr hhalf
  have hrem : p - r - t + r + t = p := by omega
  have hremQ : ((p - r - t : ℕ) : ℚ) + R + T = P := by
    dsimp only [P, R, T]
    exact_mod_cast hrem
  have hsub : ((p - r - t : ℕ) : ℚ) = P - R - T := by linarith only [hremQ]
  have hbound : R * T * (P - R - T) ≤ (N : ℚ) := by
    have hh : (r : ℚ) * (t : ℚ) * ((p - r - t : ℕ) : ℚ) ≤ (N : ℚ) := by
      exact_mod_cast hlower
    rw [hsub] at hh
    exact hh
  have hpQ : (11 : ℚ) ≤ P := by dsimp only [P]; exact_mod_cast hp
  have hrQ : (3 : ℚ) ≤ R := by dsimp only [R]; exact_mod_cast hr
  have hhalfQ : 2 * R ≤ P - 1 := by
    have hh : 2 * r + 1 ≤ p := by omega
    have hhQ : 2 * R + 1 ≤ P := by dsimp only [R, P]; exact_mod_cast hh
    linarith only [hhQ]
  have hspaceQ : 2 * T ≤ P - R := by
    have hh : 2 * t + r ≤ p := by omega
    have hhQ : 2 * T + R ≤ P := by dsimp only [T, R, P]; exact_mod_cast hh
    linarith only [hhQ]
  have hfinal : (P - 5) * (P + 1) ≤ 2 * (N : ℚ) := by
    by_cases hsmall : 2 * r ≤ p - 5
    · have hdiv : 2 ≤ (p - 2 * r + 3) / 3 := by omega
      have htlow : p - 2 * r + 1 ≤ 3 * t := by
        dsimp only [t, residualThreshold]
        rw [max_eq_right hdiv]
        omega
      have htlowQ : P - 2 * R + 1 ≤ 3 * T := by
        have hh : p + 1 ≤ 3 * t + 2 * r := by omega
        have hhQ : P + 1 ≤ 3 * T + 2 * R := by dsimp only [P, T, R]; exact_mod_cast hh
        linarith only [hhQ]
      have hsQ : 2 * R ≤ P - 5 := by
        have hh : 2 * r + 5 ≤ p := by omega
        have hhQ : 2 * R + 5 ≤ P := by dsimp only [R, P]; exact_mod_cast hh
        linarith only [hhQ]
      have hmon : 0 ≤ R * ((3 * T - (P - 2 * R + 1)) * (2 * P - R - 1 - 3 * T)) := by
        apply mul_nonneg (by linarith only [hrQ])
        apply mul_nonneg
        · linarith only [htlowQ]
        · linarith only [hspaceQ, hpQ, hrQ]
      have hquad : R * (P - 2 * R + 1) * (2 * P - R - 1) ≤
          9 * R * T * (P - R - T) := by nlinarith only [hmon]
      have hend : 0 ≤ (P - 5 - 2 * R) *
          (3 * (P - 5) + (R - 3) * (4 * P - 2 - 2 * R)) := by
        apply mul_nonneg (by linarith only [hsQ])
        apply add_nonneg
        · linarith only [hpQ]
        · exact mul_nonneg (by linarith only [hrQ]) (by linarith only [hpQ, hsQ])
      nlinarith only [hquad, hend, hbound]
    · have hdiv : (p - 2 * r + 3) / 3 ≤ 2 := by omega
      have ht : t = 2 := max_eq_left hdiv
      have htQ : T = 2 := by dsimp only [T]; exact_mod_cast ht
      have hlargeQ : P - 5 ≤ 2 * R := by
        have hh : p ≤ 2 * r + 5 := by omega
        have hhQ : P ≤ 2 * R + 5 := by dsimp only [P, R]; exact_mod_cast hh
        linarith only [hhQ]
      have hlarge : 0 ≤ (2 * R - P + 5) * (P + 1 - 2 * R) :=
        mul_nonneg (by linarith only [hlargeQ]) (by linarith only [hhalfQ])
      rw [htQ] at hbound
      nlinarith only [hlarge, hbound]
  have hp5 : 5 ≤ p := by omega
  have hpsub : ((p - 5 : ℕ) : ℚ) = P - 5 := by
    simpa only [P, Nat.cast_ofNat] using (Nat.cast_sub hp5 : ((p - 5 : ℕ) : ℚ) = (p : ℚ) - (5 : ℚ))
  have hfinalQ : ((p - 5 : ℕ) : ℚ) * ((p + 1 : ℕ) : ℚ) ≤ 2 * (N : ℚ) := by
    simpa only [hpsub, P, Nat.cast_add, Nat.cast_one] using hfinal
  exact_mod_cast hfinalQ

end Cylinder.ResidualRayArithmetic

end
