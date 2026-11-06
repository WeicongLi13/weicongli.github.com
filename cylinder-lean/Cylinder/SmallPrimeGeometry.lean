module

public import Cylinder.DirectionCurveProposition

/-! The actual first-moment relation rules out noncylinders at orders five and seven. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.SmallPrimeGeometry

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction

variable (p : ℕ) [Fact p.Prime]

theorem minimum_degree_upper {S : Finset (Geometry.Point p)} (hp : 5 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (u : directionSet p S b hb → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3)) :
    s ≤ (p - 3) / 2 := by
  let : Nonempty (directionSet p S b hb) := direction_nonempty p hcard hS hnon hb
  obtain ⟨_, _, _, htrunc⟩ := ActualCharacterBounds.full_support_character_bounds
    (representatives (embedding p) (directionSet p S b hb))
    (representatives_nonzero _ _) (representatives_distinct _ _) s hs u hu (p - 3) hrel
  have hwhite := white_card_upper_bound p hcard hS
  have htwice := twice_direction_card_le_white p hcard hS hb
  have hdiv := Nat.div_mul_le_self (p * (p - 1)) 2
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨q, hq⟩ := hodd
  have hh : 2 * ((p - 1) / 2) + 1 = p := by omega
  by_contra hbad
  have hhalf : (p - 1) / 2 ≤ s := by omega
  have hlo := htrunc ((p - 1) / 2) hhalf
  simp only [Fintype.card_coe] at hlo
  have hd : p - 3 + 3 = p := by omega
  rw [hd] at hlo
  have hsub : p - (p - 1) / 2 + (p - 1) / 2 = p := by omega
  have hminus : p - 1 + 1 = p := by omega
  nlinarith

theorem minimum_degree_bounds {S : Finset (Geometry.Point p)} (hp : 5 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 := by
  obtain ⟨u, hu, hrel⟩ := DirectionCurveProposition.full_support_direction_relation p
    (by omega) hcard hS hnon hb
  have hsup := minimum_degree_upper p hp hcard hS hnon hb s hs u hu hrel
  let D := directionSet p S b hb
  let : Nonempty D := direction_nonempty p hcard hS hnon hb
  have hspos := initialDegree_pos (representatives (embedding p) D) s hs
  obtain ⟨_, _, _, htrunc⟩ := ActualCharacterBounds.full_support_character_bounds
    (representatives (embedding p) D) (representatives_nonzero _ _)
    (representatives_distinct _ _) s hs u hu (p - 3) hrel
  have hlo := htrunc s (le_refl s)
  have hd : p - 3 + 3 = p := by omega
  simp only [hd, Fintype.card_coe] at hlo
  obtain ⟨F, hF, hF0, hzero⟩ := RationalDependentSetBounds.initial_degree_curve
    p (embedding p) D s hs
  have hzset : RationalPlaneLine.zeroSet (embedding p) D F = D := by
    apply Finset.filter_eq_self.mpr
    exact hzero
  have hsp : s < p := by omega
  have hpolar := FrobeniusPolarBound.twice_card_le p (embedding p) D
    (direction_lineCap p hcard hS hnon hb) F s hF hF0 hsp
  rw [hzset] at hpolar
  have hsub : p - s + s = p := by omega
  have hsub' : s + p - 1 + 1 = s + p := by omega
  have hthree : p + 1 ≤ 3 * s := by
    by_contra hn
    have hlt : s + p - 1 < 2 * (p - s) := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hlt hspos
    nlinarith
  refine ⟨?_, hsup⟩
  unfold DirectionExcess.threshold
  omega

theorem strongCylinderConjecture_of_five_or_seven (hp : p = 5 ∨ p = 7) :
    Geometry.StrongCylinderConjecture p := by
  intro S hcard hS
  by_contra hnon
  obtain ⟨b, hb⟩ := black_nonempty p hcard hS
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree
    (representatives (embedding p) (directionSet p S b hb))
  have hbounds := minimum_degree_bounds p (by rcases hp with rfl | rfl <;> decide)
    hcard hS hnon hb s hs
  rcases hp with hp | hp <;> rw [hp] at hbounds
  all_goals norm_num [DirectionExcess.threshold] at hbounds
  all_goals omega

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem strongCylinderConjecture_five : Geometry.StrongCylinderConjecture 5 :=
  strongCylinderConjecture_of_five_or_seven 5 (Or.inl rfl)

theorem strongCylinderConjecture_seven : Geometry.StrongCylinderConjecture 7 :=
  strongCylinderConjecture_of_five_or_seven 7 (Or.inr rfl)

end Cylinder.SmallPrimeGeometry

end
