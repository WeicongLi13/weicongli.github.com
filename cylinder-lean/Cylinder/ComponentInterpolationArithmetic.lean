module

public import Cylinder.NumericalObstruction
public import Cylinder.ManyTwoStaircase
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The bounded staircase induction and the numerical contradiction for component interpolation. -/

@[expose] public section
open scoped BigOperators

namespace Cylinder.ComponentInterpolationArithmetic

theorem staircase_to_floor (b : ℕ → ℕ) (e : ℕ) (he : 4 ≤ e) (hstart : 1 ≤ b 3)
    (hstep : ∀ m, 1 ≤ m → 4 * m + 2 < e →
      (∀ j, 1 ≤ j → j ≤ m → j ≤ b (3 * j)) → m + 1 ≤ b (3 * m + 3)) :
    ∀ j, 1 ≤ j → j ≤ (e + 1) / 4 → j ≤ b (3 * j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hja
    by_cases hj1 : j = 1
    · simpa only [hj1, Nat.mul_one] using hstart
    · have hj2 : 2 ≤ j := by omega
      have hm : 1 ≤ j - 1 := by omega
      have hsmall : 4 * (j - 1) + 2 < e := by omega
      have hstair : ∀ k, 1 ≤ k → k ≤ j - 1 → k ≤ b (3 * k) := by
        intro k hk hkj
        exact ih k (by omega) hk (by omega)
      have hh := hstep (j - 1) hm hsmall hstair
      have hjrem : j - 1 + 1 = j := by omega
      have hindex : 3 * (j - 1) + 3 = 3 * j := by omega
      simpa only [hjrem, hindex] using hh

theorem staircase_incompatible_with_component_bounds (p s e δ ell : ℕ)
    (he : 4 ≤ e) (hδ : 3 ≤ δ) (hes : e ≤ s) (hδe : δ + 1 ≤ e)
    (hp : p = 2 * s + δ) (hexcess : 4 * ell + p ≤ δ ^ 2 + 2)
    (hpolar : 2 * ell ≤ e * (e - δ - 1))
    (hlower : 2 * ((e + 1) / 4) * e ≤
      2 * ell + 3 * ((e + 1) / 4) * ((e + 1) / 4 + 1)) : False := by
  let z : ℝ := (δ : ℝ) + 2 * e
  have hδR : (3 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hesR : (e : ℝ) ≤ (s : ℝ) := by exact_mod_cast hes
  have hpR : (p : ℝ) = 2 * s + δ := by exact_mod_cast hp
  have hz : 2 * (e : ℝ) + 3 ≤ z := by dsimp [z]; linarith
  have hzp : z ≤ (p : ℝ) := by dsimp [z]; linarith
  have hexcessR : 4 * (ell : ℝ) + p ≤ (δ : ℝ) ^ 2 + 2 := by exact_mod_cast hexcess
  have hpolarR : 2 * (ell : ℝ) ≤ (e : ℝ) * ((e - δ - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpolar
  have hrem : e - δ - 1 + δ + 1 = e := by omega
  have hremR : ((e - δ - 1 : ℕ) : ℝ) + δ + 1 = e := by exact_mod_cast hrem
  have hlowerR : 2 * (((e + 1) / 4 : ℕ) : ℝ) * e ≤
      2 * (ell : ℝ) + 3 * (((e + 1) / 4 : ℕ) : ℝ) * ((((e + 1) / 4 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hlower
  have hcorr : (((e + 1) / 4 : ℕ) : ℝ) * e -
      (3 / 2 : ℝ) * (((e + 1) / 4 : ℕ) : ℝ) * ((((e + 1) / 4 : ℕ) : ℝ) + 1) ≤ ell := by
    nlinarith only [hlowerR]
  have hfirst : (e : ℝ) * (z - e) + ell ≤ (z ^ 2 - z + 2) / 4 := by
    dsimp [z] at hzp ⊢
    nlinarith only [hexcessR, hzp]
  have hsecond : (e : ℝ) * (z - e) + ell ≤ (e : ℝ) * ((e : ℝ) + z - 1) / 2 := by
    dsimp [z]
    nlinarith only [hpolarR, hremR]
  have hob := Cylinder.Numerical.numerical_obstruction e he z hz
  dsimp only at hob
  have htotal : (e : ℝ) * (z - e) + (((e + 1) / 4 : ℕ) : ℝ) * e -
      (3 / 2 : ℝ) * (((e + 1) / 4 : ℕ) : ℝ) * ((((e + 1) / 4 : ℕ) : ℝ) + 1) ≤
      (e : ℝ) * (z - e) + ell := by linarith only [hcorr]
  exact (not_le_of_gt hob) (htotal.trans (le_min hfirst hsecond))

theorem zero_third_or_plateau (b : ℕ → ℕ) (p s e δ ell : ℕ)
    (he : 4 ≤ e) (hδ : 3 ≤ δ) (hes : e ≤ s) (hδe : δ + 1 ≤ e)
    (hp : p = 2 * s + δ) (hexcess : 4 * ell + p ≤ δ ^ 2 + 2)
    (hpolar : 2 * ell ≤ e * (e - δ - 1))
    (hinc : ∀ j, j + 1 < e → b j ≤ b (j + 1))
    (hsum : (∑ i ∈ Finset.range e, b i) = ell) :
    b 3 = 0 ∨ ∃ m, 1 ≤ m ∧ 4 * m + 2 < e ∧
      (∀ j, 1 ≤ j → j ≤ m → j ≤ b (3 * j)) ∧
      ∀ r < 4, b (3 * m + r) = m := by
  by_cases hb3 : b 3 = 0
  · exact Or.inl hb3
  · apply Or.inr
    by_contra hnot
    have hstep : ∀ m, 1 ≤ m → 4 * m + 2 < e →
        (∀ j, 1 ≤ j → j ≤ m → j ≤ b (3 * j)) → m + 1 ≤ b (3 * m + 3) := by
      intro m hm hsmall hstair
      by_contra hnext
      have hupper : b (3 * m + 3) ≤ m := by omega
      have hplateau : ∀ r < 4, b (3 * m + r) = m := by
        intro r hr
        have hlo := (hstair m hm le_rfl).trans
          (ManyTwoStaircase.monotone_on_prefix b e hinc (3 * m) (3 * m + r) (by omega) (by omega))
        have hhi := (ManyTwoStaircase.monotone_on_prefix b e hinc (3 * m + r)
          (3 * m + 3) (by omega) (by omega)).trans hupper
        omega
      exact hnot ⟨m, hm, hsmall, hstair, hplateau⟩
    have hstair := staircase_to_floor b e he (by omega) hstep
    have hlo := ManyTwoStaircase.staircase_bound b e ((e + 1) / 4) (by omega) hinc hstair
    rw [hsum] at hlo
    exact staircase_incompatible_with_component_bounds p s e δ ell he hδ hes hδe hp hexcess hpolar hlo

end Cylinder.ComponentInterpolationArithmetic

end
