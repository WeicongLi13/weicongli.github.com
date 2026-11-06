module

public import Cylinder.SimpleBlackWeights

/-! The direction count and ray excess for the actual black-point projection. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.DirectionExcess

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection

variable (p : ℕ) [Fact p.Prime]

def threshold : ℕ := (p + 3) / 3

def directionLowerBound : ℕ := threshold p * (p - threshold p)

def rayExcess (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) : ℕ :=
  ∑ i : directionSet p S b hb, (raySize p S b hb i - 2)

def largeRays (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) : Finset (directionSet p S b hb) :=
  Finset.univ.filter (fun i => 3 ≤ raySize p S b hb i)

/-- The number of actual directions is at least the manuscript's G_p. -/
theorem direction_count_lower {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    directionLowerBound p ≤ (directionSet p S b hb).card := by
  obtain ⟨i, hi⟩ := SimpleBlackWeights.exists_two_point_ray p hcard hS hnon hb
  have hmin : ∀ i : directionSet p S b hb, 2 ≤ raySize p S b hb i :=
    fun i => two_le_raySize p hcard hS hb i
  have hhalf : 2 ≤ (p - 1) / 2 := by
    have h := raySize_le_half p hcard hS hnon hb i
    rwa [hi] at h
  have hp : 5 ≤ p := by omega
  have hcap := BlackProjectionRationalLines.lineCap p hcard hS hnon hb 2 (by decide) hmin
  have hdep := BlackProjectionVandermonde.dependent_in_degree_of_ray p
    (K := AlgebraicClosure (ZMod p)) hcard hS hnon hb i
  rw [hi] at hdep
  have hbound := RationalDependentSetBounds.dependent_set_lower p
    (ProductEvaluationRelation.primeEmbedding p (K := AlgebraicClosure (ZMod p)))
    (directionSet p S b hb) 2 (le_refl 2) hhalf hcap hdep
  have heq : BlackRayArithmetic.rayCeiling p 2 = threshold p := by
    unfold BlackRayArithmetic.rayCeiling threshold
    congr 1
    omega
  simpa only [directionLowerBound, heq, Nat.sub_add_cancel (by omega : 2 ≤ p)] using hbound

theorem ray_excess_identity {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    rayExcess p S b hb = (whitePoints p S).card - 2 * (directionSet p S b hb).card := by
  have hpoint : ∀ i : directionSet p S b hb,
      (raySize p S b hb i - 2) + 2 = raySize p S b hb i := by
    intro i
    have h := two_le_raySize p hcard hS hb i
    omega
  have hsum := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (directionSet p S b hb))) => hpoint i)
  rw [Finset.sum_add_distrib, sum_raySize p hb] at hsum
  change rayExcess p S b hb + (∑ _i : directionSet p S b hb, (2 : ℕ)) =
    (whitePoints p S).card at hsum
  have hconstant : (∑ _i : directionSet p S b hb, (2 : ℕ)) =
      2 * (directionSet p S b hb).card := by simp [mul_comm]
  rw [hconstant] at hsum
  omega

theorem ray_excess_upper {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    rayExcess p S b hb ≤ (whitePoints p S).card - 2 * directionLowerBound p := by
  rw [ray_excess_identity p hcard hS hb]
  have hcount := direction_count_lower p hcard hS hnon hb
  omega

theorem large_rays_card_le_excess {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    (largeRays p S b hb).card ≤ rayExcess p S b hb := by
  calc
    _ = ∑ _i ∈ largeRays p S b hb, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ largeRays p S b hb, (raySize p S b hb i - 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      omega
    _ ≤ ∑ i : directionSet p S b hb, (raySize p S b hb i - 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := rfl

/-- All assertions of Corollary `cor:excess` concern actual directions and rays. -/
theorem direction_excess_bounds {S : Finset (Geometry.Point p)} (_hp : 5 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    directionLowerBound p ≤ (directionSet p S b hb).card ∧
    rayExcess p S b hb = (whitePoints p S).card - 2 * (directionSet p S b hb).card ∧
    rayExcess p S b hb ≤ (whitePoints p S).card - 2 * directionLowerBound p ∧
    (largeRays p S b hb).card ≤ rayExcess p S b hb :=
  ⟨direction_count_lower p hcard hS hnon hb, ray_excess_identity p hcard hS hb,
    ray_excess_upper p hcard hS hnon hb, large_rays_card_le_excess p hb⟩

end Cylinder.DirectionExcess

end
