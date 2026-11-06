module

public import Cylinder.DirectionCurveProposition

/-! Counts of the actual exclusive components and their two-point rays. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.DirectionCurveComponentCounting

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.MinimumEquationComponentSets
open Cylinder.PlaneCurveFactors Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.DirectionCurveProposition

variable {K : Type*} [Field K]

theorem componentPoints_subset (D : Finset (PlanePoint K))
    (F G : MvPolynomial (Fin 3) K) : componentPoints D F G ⊆ D :=
  Finset.filter_subset _ _

theorem component_card_sum_le (D : Finset (PlanePoint K))
    (F : MvPolynomial (Fin 3) K) :
    (∑ G ∈ factors F, (componentPoints D F G).card) ≤ D.card := by
  have hdisj : (factors F : Set (MvPolynomial (Fin 3) K)).PairwiseDisjoint
      (componentPoints D F) := by
    intro G _hG Q hQ hGQ
    exact componentPoints_disjoint D F G Q hQ hGQ
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro P hP
  obtain ⟨G, _hG, hPG⟩ := Finset.mem_biUnion.mp hP
  exact componentPoints_subset D F G hPG

theorem component_card_add_other_sum_le (D : Finset (PlanePoint K))
    (F G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) :
    (componentPoints D F G).card +
      (∑ Q ∈ (factors F).erase G, (componentPoints D F Q).card) ≤ D.card := by
  rw [Finset.add_sum_erase (factors F) (fun Q => (componentPoints D F Q).card) hG]
  exact component_card_sum_le D F

theorem component_card_degree_bound (D : Finset (PlanePoint K))
    (F G : MvPolynomial (Fin 3) K) (s a : ℕ) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hG : G ∈ factors F)
    (hlo : ∀ Q ∈ factors F, Q.totalDegree * a ≤ (componentPoints D F Q).card) :
    (componentPoints D F G).card + (s - G.totalDegree) * a ≤ D.card := by
  have hdegrees := factors_degree_sum_eq F hF0 hsq
  rw [hF.totalDegree hF0] at hdegrees
  have hdegrees' := Finset.add_sum_erase (factors F) (fun Q => Q.totalDegree) hG
  rw [hdegrees] at hdegrees'
  have hrem : (∑ Q ∈ (factors F).erase G, Q.totalDegree) = s - G.totalDegree := by
    omega
  have hsum := Finset.sum_le_sum (s := (factors F).erase G)
    (fun Q hQ => hlo Q (Finset.mem_of_mem_erase hQ))
  rw [← Finset.sum_mul, hrem] at hsum
  exact (Nat.add_le_add_left hsum _).trans (component_card_add_other_sum_le D F G hG)

variable (p : ℕ) [Fact p.Prime]

theorem actual_component_card_bound {S : Finset (Geometry.Point p)}
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hG : G ∈ factors F)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    (componentPoints (directionSet p S b hb) F G).card +
      (s - G.totalDegree) * (p - s) ≤ (directionSet p S b hb).card := by
  apply component_card_degree_bound _ F G s (p - s) hF hF0 hsq hG
  intro Q hQ
  obtain ⟨H, hQH⟩ := factor_dvd F Q hQ
  have hdata := hcomp Q hQ H hQH
  rw [← hdata.1]
  exact hdata.2.2.2.2.1

def twoPointDirections {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (E : Finset (directionSet p S b hb)) :
    Finset (directionSet p S b hb) := E.filter (fun i => raySize p S b hb i = 2)

theorem two_point_directions_and_excess {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (E : Finset (directionSet p S b hb)) :
    E.card ≤ (twoPointDirections p hb E).card + DirectionExcess.rayExcess p S b hb := by
  have hcount := Finset.card_filter_add_card_filter_not (s := E)
    (fun i => raySize p S b hb i = 2)
  have hsub : E.filter (fun i => ¬raySize p S b hb i = 2) ⊆
      DirectionExcess.largeRays p S b hb := by
    intro i hi
    have hnot := (Finset.mem_filter.mp hi).2
    have hmin := two_le_raySize p hcard hS hb i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
  have hlarge := (Finset.card_le_card hsub).trans
    (DirectionExcess.large_rays_card_le_excess p hb)
  change (twoPointDirections p hb E).card +
    (E.filter (fun i => ¬raySize p S b hb i = 2)).card = E.card at hcount
  omega

theorem two_point_directions_count_lower {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (E : Finset (directionSet p S b hb)) :
    E.card + 2 * (directionSet p S b hb).card ≤
      (twoPointDirections p hb E).card + (whitePoints p S).card := by
  have hlo := two_point_directions_and_excess p hcard hS hb E
  rw [DirectionExcess.ray_excess_identity p hcard hS hb] at hlo
  have htwice := DirectionCurveBounds.twice_direction_card_le_white p hcard hS hb
  omega

def componentDirections {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (F G : MvPolynomial (Fin 3) (ZMod p)) :
    Finset (directionSet p S b hb) :=
  (componentPoints (directionSet p S b hb) F G).subtype (fun P => P ∈ directionSet p S b hb)

theorem componentDirections_card {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (F G : MvPolynomial (Fin 3) (ZMod p)) :
    (componentDirections p hb F G).card = (componentPoints (directionSet p S b hb) F G).card := by
  unfold componentDirections
  rw [Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  exact componentPoints_subset _ F G

/-- The actual two-point directions on a component satisfy the estimate
used before the final strict numerical comparison in the manuscript. -/
theorem actual_two_point_component_count_lower {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hG : G ∈ factors F)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    3 * (componentPoints (directionSet p S b hb) F G).card +
      2 * (s - G.totalDegree) * (p - s) ≤
      (twoPointDirections p hb (componentDirections p hb F G)).card + (whitePoints p S).card := by
  have htwo := two_point_directions_count_lower p hcard hS hb (componentDirections p hb F G)
  rw [componentDirections_card] at htwo
  have hk := actual_component_card_bound p hb s F G hF hF0 hsq hG hcomp
  nlinarith

def componentExcess {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (F G : MvPolynomial (Fin 3) (ZMod p)) : ℕ :=
  (componentPoints (directionSet p S b hb) F G).card - G.totalDegree * (p - s)

theorem componentExcess_identity {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (F G : MvPolynomial (Fin 3) (ZMod p))
    (hG : G ∈ factors F) (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    G.totalDegree * (p - s) + componentExcess p hb s F G =
      (componentPoints (directionSet p S b hb) F G).card := by
  obtain ⟨H, hGH⟩ := factor_dvd F G hG
  have hdata := hcomp G hG H hGH
  have hlo := hdata.2.2.2.2.1
  rw [hdata.1] at hlo
  unfold componentExcess
  omega

theorem actual_two_point_component_excess_bound {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hG : G ∈ factors F)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    (2 * s + G.totalDegree) * (p - s) + 3 * componentExcess p hb s F G ≤
      (twoPointDirections p hb (componentDirections p hb F G)).card + (whitePoints p S).card := by
  have htwo := actual_two_point_component_count_lower p hcard hS hb s F G hF hF0 hsq hG hcomp
  have hexcess := componentExcess_identity p hb s F G hG hcomp
  have hse := totalDegree_le_of_dvd_of_isDomain (factor_dvd F G hG) hF0
  rw [hF.totalDegree hF0] at hse
  have hsub : s - G.totalDegree + G.totalDegree = s := Nat.sub_add_cancel hse
  nlinarith

end Cylinder.DirectionCurveComponentCounting

end
