module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Meta.Tactic.NormCast

/-!
# The numerical obstruction in the cylinder paper

This file formalizes Lemma `lem:numericalobstruction` in `cylinder.tex`.
The degree is a natural number, and `(e + 1) / 4` is natural-number
division, hence the floor used in the paper.  The variable `z` is real.

The argument proves the floor bounds and the complete strict inequality;
it does not assume any geometric estimates from the paper.
-/

public section

namespace Cylinder.Numerical

/-- The lower bound for the correction term used in
Lemma `lem:numericalobstruction`. -/
theorem correction_lower_bound (e : ℕ) (he : 4 ≤ e) :
    let a : ℕ := (e + 1) / 4
    (a : ℝ) * (e : ℝ) - (3 / 2 : ℝ) * (a : ℝ) * ((a : ℝ) + 1) ≥
      (e : ℝ) * (5 * (e : ℝ) - 16) / 32 := by
  dsimp only
  have heR : (4 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have haLowerNat : e ≤ 4 * ((e + 1) / 4) + 2 := by omega
  have haUpperNat : 4 * ((e + 1) / 4) ≤ e + 1 := by omega
  have haLower : 0 ≤ 4 * (((e + 1) / 4 : ℕ) : ℝ) - (e : ℝ) + 2 := by
    have h : (e : ℝ) ≤ 4 * (((e + 1) / 4 : ℕ) : ℝ) + 2 := by
      exact_mod_cast haLowerNat
    linarith
  have haUpper : 0 ≤ (e : ℝ) + 1 - 4 * (((e + 1) / 4 : ℕ) : ℝ) := by
    have h : 4 * (((e + 1) / 4 : ℕ) : ℝ) ≤ (e : ℝ) + 1 := by
      exact_mod_cast haUpperNat
    linarith
  have hConcavity := mul_nonneg haLower haUpper
  have hDegree := mul_nonneg (sub_nonneg.mpr heR) haLower
  nlinarith only [haLower, haUpper, hConcavity, hDegree]

/-- Lemma `lem:numericalobstruction`, with the integer floor encoded by
natural-number division. -/
theorem numerical_obstruction (e : ℕ) (he : 4 ≤ e)
    (z : ℝ) (hz : 2 * (e : ℝ) + 3 ≤ z) :
    let a : ℕ := (e + 1) / 4
    (e : ℝ) * (z - (e : ℝ)) + (a : ℝ) * (e : ℝ) -
        (3 / 2 : ℝ) * (a : ℝ) * ((a : ℝ) + 1) >
      min ((z ^ 2 - z + 2) / 4) ((e : ℝ) * ((e : ℝ) + z - 1) / 2) := by
  dsimp only
  have heR : (4 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hePos : (0 : ℝ) < (e : ℝ) := by linarith
  have hCorrection := correction_lower_bound e he
  dsimp only at hCorrection
  by_contra hNot
  have hBoth :
      (e : ℝ) * (z - (e : ℝ)) + (((e + 1) / 4 : ℕ) : ℝ) * (e : ℝ) -
          (3 / 2 : ℝ) * (((e + 1) / 4 : ℕ) : ℝ) *
            ((((e + 1) / 4 : ℕ) : ℝ) + 1) ≤
        min ((z ^ 2 - z + 2) / 4) ((e : ℝ) * ((e : ℝ) + z - 1) / 2) :=
    le_of_not_gt hNot
  have hFirst := le_trans hBoth (min_le_left _ _)
  have hSecond := le_trans hBoth (min_le_right _ _)
  have hzUpper : z ≤ 43 * (e : ℝ) / 16 := by
    by_contra h
    have hPositive : 0 < (e : ℝ) * (z - 43 * (e : ℝ) / 16) :=
      mul_pos hePos (by linarith)
    nlinarith only [hCorrection, hSecond, hPositive]
  have hPolynomial :
      0 ≤ z ^ 2 - (4 * (e : ℝ) + 1) * z + 4 * (e : ℝ) ^ 2 -
        (e : ℝ) * (5 * (e : ℝ) - 16) / 8 + 2 := by
    nlinarith only [hCorrection, hFirst]
  have hMonotonicity :
      0 ≤ (43 * (e : ℝ) / 16 - z) *
        (43 * (e : ℝ) / 16 + z - (4 * (e : ℝ) + 1)) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hEndpoint :
      -(39 : ℝ) * (e : ℝ) ^ 2 / 256 - 11 * (e : ℝ) / 16 + 2 < 0 := by
    nlinarith only [heR, sq_nonneg (e : ℝ)]
  nlinarith only [hPolynomial, hMonotonicity, hEndpoint]

end Cylinder.Numerical
