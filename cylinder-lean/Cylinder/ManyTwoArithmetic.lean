module

public import Cylinder.BlackRayArithmetic

/-! The strict numerical comparison used in the many-two-point-rays lemma. -/

@[expose] public section

namespace Cylinder.ManyTwoArithmetic

theorem many_two_strict (p s e δ m ell n u : ℕ)
    (hpeq : p = 2 * s + δ) (hse : e ≤ s) (hδe : δ + 1 ≤ e) (hδ : 3 ≤ δ)
    (_hm : 1 ≤ m) (hme : 4 * m + 2 < e)
    (hn : 2 * n ≤ p * (p - 1) + 2)
    (hell : 2 * m * e ≤ 2 * ell + 3 * m * (m + 1))
    (hlower : (2 * s + e) * (p - s) + 3 * ell ≤ u + n) :
    e * (5 * m + 2) < u := by
  let P : ℤ := p
  let S : ℤ := s
  let E : ℤ := e
  let De : ℤ := δ
  let M : ℤ := m
  let L : ℤ := ell
  let N : ℤ := n
  let U : ℤ := u
  have hP : P = 2 * S + De := by dsimp [P, S, De]; exact_mod_cast hpeq
  have hSE : E ≤ S := by dsimp [E, S]; exact_mod_cast hse
  have hDE : De + 1 ≤ E := by dsimp [De, E]; exact_mod_cast hδe
  have hD : 3 ≤ De := by dsimp [De]; exact_mod_cast hδ
  have hE0 : 0 ≤ E := by dsimp [E]; exact_mod_cast Nat.zero_le e
  have hM0 : 0 ≤ M := by dsimp [M]; exact_mod_cast Nat.zero_le m
  have hME : 4 * M + 3 ≤ E := by
    have h : 4 * m + 3 ≤ e := by omega
    dsimp [M, E]
    exact_mod_cast h
  have hp1 : 1 ≤ p := by omega
  have hsp : s ≤ p := by omega
  have hN : 2 * N ≤ P * (P - 1) + 2 := by
    have h : (2 : ℤ) * n ≤ ((p * (p - 1) + 2 : ℕ) : ℤ) := by exact_mod_cast hn
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one, Nat.cast_ofNat] using h
  have hL : 2 * M * E ≤ 2 * L + 3 * M * (M + 1) := by
    dsimp [M, E, L]
    exact_mod_cast hell
  have hU : (2 * S + E) * (P - S) + 3 * L ≤ U + N := by
    have h : (((2 * s + e) * (p - s) + 3 * ell : ℕ) : ℤ) ≤ (u : ℤ) + n := by
      exact_mod_cast hlower
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsp, Nat.cast_ofNat] using h
  by_contra hsmall
  have hsmallN : u ≤ e * (5 * m + 2) := by omega
  have hsmallZ : U ≤ E * (5 * M + 2) := by dsimp [U, E, M]; exact_mod_cast hsmallN
  have hmrem : 0 ≤ E - 3 - 4 * M := by omega
  have hmfactor : 0 ≤ 25 * E + 36 * M + 9 := by omega
  have hmprod := mul_nonneg hmrem hmfactor
  have hmbound : 64 * M * E + 144 * M * (M + 1) + 66 * E + 27 ≤ 25 * E ^ 2 := by
    nlinarith only [hmprod]
  have hrest := mul_nonneg (show 0 ≤ S - E by omega) (show 0 ≤ E + 1 by omega)
  have hdelta := mul_nonneg (show 0 ≤ De by omega) (show 0 ≤ 2 * E - De by omega)
  have hid : 32 * (2 * S + E) * (P - S) - 25 * E ^ 2 + 2 * E - 16 * P ^ 2 + 16 * P - 5 =
      7 * E ^ 2 + 32 * (S - E) * (E + 1) + 16 * De * (2 * E - De) + 34 * E + 16 * De - 5 := by
    rw [hP]
    ring
  have hpositive : 0 < 32 * (2 * S + E) * (P - S) - 25 * E ^ 2 +
      2 * E - 16 * P ^ 2 + 16 * P - 5 := by
    nlinarith only [hid, hrest, hdelta, sq_nonneg E, hD, hDE]
  nlinarith only [hN, hL, hU, hsmallZ, hmbound, hpositive]

end Cylinder.ManyTwoArithmetic

end
