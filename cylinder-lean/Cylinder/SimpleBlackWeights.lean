module

public import Cylinder.RationalDependentSetBounds
public import Cylinder.BlackProjectionVandermonde
public import Cylinder.BlackProjectionRationalLines
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The complete black-weight proposition on the original affine point set. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.SimpleBlackWeights

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.BlackRayArithmetic

variable (p : ℕ) [Fact p.Prime]

theorem minimum_two_over_field {K : Type*} [Field K] [CharP K p] [IsAlgClosed K]
    {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ i : directionSet p S b hb, raySize p S b hb i = 2 := by
  obtain ⟨r, hr, hrp, ⟨i, hi⟩, hmin, hrd, _hline⟩ :=
    BlackProjectionLineCap.exists_minimum_with_bounds p hcard hS hnon hb
  have hcap := BlackProjectionRationalLines.lineCap p hcard hS hnon hb r (by omega) hmin
  have hdep := BlackProjectionVandermonde.dependent_in_degree_of_ray p (K := K)
    hcard hS hnon hb i
  rw [hi] at hdep
  have hlength := RationalDependentSetBounds.dependent_set_lower p
    (ProductEvaluationRelation.primeEmbedding p (K := K)) (directionSet p S b hb) r hr hrp hcap hdep
  have hlower : r * rayCeiling p r * (p - r + 2 - rayCeiling p r) ≤ (whitePoints p S).card := by
    simpa only [mul_assoc] using (Nat.mul_le_mul_left r hlength).trans hrd
  have hn := white_card_upper_bound p hcard hS
  have hr2 : r = 2 := by
    by_contra hne
    have hr3 : 3 ≤ r := by omega
    have hp7 : 7 ≤ p := by omega
    exact ray_ceiling_contradiction p r (whitePoints p S).card hp7 hr3 hrp hn hlower
  exact ⟨i, hi.trans hr2⟩

/-- No extension-field assumption remains: the curve argument is carried
out in the actual algebraic closure of the prime field. -/
theorem exists_two_point_ray {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ i : directionSet p S b hb, raySize p S b hb i = 2 :=
  minimum_two_over_field p (K := AlgebraicClosure (ZMod p)) hcard hS hnon hb

theorem black_weight_eq_one {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) : weight p S b = 1 := by
  obtain ⟨i, hi⟩ := exists_two_point_ray p hcard hS hnon hb
  have hbound := ProjectiveBlackLine.weight_add_one_le_white_on_line p hcard hS
    (rayDualSpace p b i.val) (rayDualSpace_finrank p b i.val) (white_ray_nonempty p hb i)
    b hb (black_mem_rayDualSpace p b i.val)
  rw [← raySize_white_card p hb i, hi] at hbound
  have hpos := ProjectiveLineCap.black_weight_pos p hb
  omega

theorem white_card_exact {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) :
    (whitePoints p S).card = 1 + p * (p - 1) / 2 := by
  have hw : ∀ b ∈ blackPoints p S, weight p S b = 1 :=
    fun b hb => black_weight_eq_one p hcard hS hnon hb
  have hsum : (∑ b ∈ blackPoints p S, weight p S b) = (blackPoints p S).card := by
    calc
      _ = ∑ _b ∈ blackPoints p S, (1 : ℕ) :=
        Finset.sum_congr rfl (fun b hb => hw b hb)
      _ = _ := by simp
  have henergy : (blackPoints p S).card * 2 = p * (p - 1) := by
    calc
      _ = ∑ _b ∈ blackPoints p S, (2 : ℕ) := by simp
      _ = ∑ b ∈ blackPoints p S, weight p S b * (weight p S b + 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hw b hb]
      _ = _ := sum_black_energy p hcard hS
  have hwhite := WhiteBlackWeights.white_card_eq_sum_black_weight_add_one
    (Finset.univ : Finset (DualPoint p)) (quotient p S) (quotient_total p S hcard hS)
  change (whitePoints p S).card = (∑ b ∈ blackPoints p S, weight p S b) + 1 at hwhite
  rw [hsum] at hwhite
  omega

theorem plane_intersection_sizes {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (H : DualPoint p) :
    (intersection p S H).card ∈ ({0, p, 2 * p} : Finset ℕ) := by
  have hquot : quotient p S H ≤ 2 := by
    by_cases hb : H ∈ blackPoints p S
    · have hw := black_weight_eq_one p hcard hS hnon hb
      have hq : 2 ≤ quotient p S H := (Finset.mem_filter.mp hb).2
      unfold weight at hw
      omega
    · have hq : ¬2 ≤ quotient p S H :=
        fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
  have hmul := p_mul_quotient p hS H
  interval_cases hq : quotient p S H <;>
    simp only [hq, mul_zero, mul_one, mul_comm p 2] at hmul <;>
    simp [← hmul]

/-- All assertions of Proposition `prop:simple`, for the original
configuration under the noncylinder hypotheses of the manuscript. -/
theorem simple_black_points {S : Finset (Geometry.Point p)} (hp : 5 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) :
    (∀ b ∈ blackPoints p S, weight p S b = 1) ∧
    (whitePoints p S).card = 1 + p * (p - 1) / 2 ∧
    (∀ H : DualPoint p, (intersection p S H).card ∈ ({0, p, 2 * p} : Finset ℕ)) ∧
    ∀ b : DualPoint p, ∀ hb : b ∈ blackPoints p S,
      ∃ i : directionSet p S b hb, raySize p S b hb i = 2 := by
  exact ⟨fun _ hb => black_weight_eq_one p hcard hS hnon hb,
    white_card_exact p hcard hS hnon,
    plane_intersection_sizes p hcard hS hnon,
    fun _ hb => exists_two_point_ray p hcard hS hnon hb⟩

end Cylinder.SimpleBlackWeights

end
