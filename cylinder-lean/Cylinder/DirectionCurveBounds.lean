module

public import Cylinder.DirectionExcess
public import Cylinder.MinimumEquationAbsoluteFactors

/-!
The numerical bounds for the minimum curve through the actual black
direction set. The first-moment relation is an explicit input; all ray,
line, character and polar estimates are derived from the configuration.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.DirectionCurveBounds

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneBinaryReduction Cylinder.MinimumEquationReduced

variable (p : ℕ) [Fact p.Prime]

abbrev CurveField := AlgebraicClosure (ZMod p)

def embedding : ZMod p →+* CurveField p := algebraMap (ZMod p) (CurveField p)

theorem twice_direction_card_le_white {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    2 * (directionSet p S b hb).card ≤ (whitePoints p S).card := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (directionSet p S b hb)))
    (f := fun _ => (2 : ℕ)) (g := raySize p S b hb)
    (fun i _ => two_le_raySize p hcard hS hb i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.nsmul_eq_mul,
    mul_comm, sum_raySize p hb] using h

theorem direction_nonempty {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    Nonempty (directionSet p S b hb) := by
  obtain ⟨i, _⟩ := SimpleBlackWeights.exists_two_point_ray p hcard hS hnon hb
  exact ⟨i⟩

theorem direction_lineCap {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    LineCap (directionSet p S b hb) ((p - 1) / 2) :=
  BlackProjectionRationalLines.lineCap p hcard hS hnon hb 2 (by decide)
    (fun i => two_le_raySize p hcard hS hb i)

theorem initial_degree_upper {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
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

theorem numerical_bounds {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (u : directionSet p S b hb → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3)) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (whitePoints p S).card / 2 ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 := by
  let D := directionSet p S b hb
  let : Nonempty D := direction_nonempty p hcard hS hnon hb
  have hspos := initialDegree_pos (representatives (embedding p) D) s hs
  have hsup := initial_degree_upper p hp hcard hS hnon hb s hs u hu hrel
  obtain ⟨_, _, _, htrunc⟩ := ActualCharacterBounds.full_support_character_bounds
    (representatives (embedding p) D) (representatives_nonzero _ _)
    (representatives_distinct _ _) s hs u hu (p - 3) hrel
  have hlo := htrunc s (le_refl s)
  have hd : p - 3 + 3 = p := by omega
  simp only [hd, Fintype.card_coe] at hlo
  obtain ⟨F, hF, hF0, hzero⟩ := RationalDependentSetBounds.initial_degree_curve
    p (embedding p) D s hs
  have hzset : zeroSet (embedding p) D F = D := by
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
  refine ⟨?_, hsup, hlo, ?_, ?_⟩
  · unfold DirectionExcess.threshold
    omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    simpa only [mul_comm] using twice_direction_card_le_white p hcard hS hb
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    simpa only [mul_comm] using hpolar

end Cylinder.DirectionCurveBounds

end
