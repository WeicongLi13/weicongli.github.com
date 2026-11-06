module

public import Cylinder.DirectionCurveComponentCounting
public import Cylinder.IntersectionZeroSet

/-! The actual exclusive-component decomposition and its excess bounds. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.DirectionComponentDecomposition

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCurveFactors
open Cylinder.MinimumEquationComponentSets Cylinder.DirectionCurveComponentCounting
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveProposition

variable {K : Type*} [Field K]

def exclusiveUnion (D : Finset (PlanePoint K)) (F : MvPolynomial (Fin 3) K) :
    Finset (PlanePoint K) := (factors F).biUnion (componentPoints D F)

def intersectionPoints (D : Finset (PlanePoint K)) (F : MvPolynomial (Fin 3) K) :
    Finset (PlanePoint K) := D \ exclusiveUnion D F

theorem exclusiveUnion_subset (D : Finset (PlanePoint K)) (F : MvPolynomial (Fin 3) K) :
    exclusiveUnion D F ⊆ D := by
  intro P hP
  obtain ⟨G, _hG, hPG⟩ := Finset.mem_biUnion.mp hP
  exact componentPoints_subset D F G hPG

theorem component_card_decomposition (D : Finset (PlanePoint K))
    (F : MvPolynomial (Fin 3) K) :
    (intersectionPoints D F).card + (∑ G ∈ factors F, (componentPoints D F G).card) = D.card := by
  have hdisj : (factors F : Set (MvPolynomial (Fin 3) K)).PairwiseDisjoint
      (componentPoints D F) := by
    intro G _hG Q hQ hGQ
    exact componentPoints_disjoint D F G Q hQ hGQ
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_sdiff_add_card_eq_card (exclusiveUnion_subset D F)

theorem intersectionPoints_subset (D : Finset (PlanePoint K)) (F : MvPolynomial (Fin 3) K) :
    intersectionPoints D F ⊆ D := Finset.sdiff_subset

theorem intersectionPoints_multiple (D : Finset (PlanePoint K))
    (F : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    ∀ P ∈ intersectionPoints D F,
      ∃ G ∈ factors F, ∃ Q ∈ factors F, G ≠ Q ∧ eval P.rep G = 0 ∧ eval P.rep Q = 0 := by
  intro P hP
  obtain ⟨hPD, hnot⟩ := Finset.mem_sdiff.mp hP
  obtain ⟨G, hG, hGzero⟩ := (eval_zero_iff_factor_zero F hF0 P.rep).mp (hzero P hPD)
  have hnotG : P ∉ componentPoints D F G := by
    intro hPG
    exact hnot (Finset.mem_biUnion.mpr ⟨G, hG, hPG⟩)
  have hnotothers : ¬∀ Q ∈ (factors F).erase G, eval P.rep Q ≠ 0 := by
    intro hothers
    exact hnotG (Finset.mem_filter.mpr ⟨hPD, hGzero, hothers⟩)
  push_neg at hnotothers
  obtain ⟨Q, hQ, hQzero⟩ := hnotothers
  obtain ⟨hQG, hQF⟩ := Finset.mem_erase.mp hQ
  exact ⟨G, hG, Q, hQF, hQG.symm, hGzero, hQzero⟩

theorem component_and_intersection_card_le (D : Finset (PlanePoint K))
    (F G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) :
    (componentPoints D F G).card + (intersectionPoints D F).card ≤ D.card := by
  have hdisj : Disjoint (componentPoints D F G) (intersectionPoints D F) := by
    apply Finset.disjoint_left.mpr
    intro P hPG hPJ
    exact (Finset.mem_sdiff.mp hPJ).2 (Finset.mem_biUnion.mpr ⟨G, hG, hPG⟩)
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.union_subset (componentPoints_subset D F G)
    (intersectionPoints_subset D F))

variable (p : ℕ) [Fact p.Prime]

def totalExcess {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) : ℕ :=
  (directionSet p S b hb).card - s * (p - s)

theorem total_excess_decomposition {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (F : MvPolynomial (Fin 3) (ZMod p))
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hsq : Squarefree F)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    totalExcess p hb s = (intersectionPoints (directionSet p S b hb) F).card +
      (∑ G ∈ factors F, componentExcess p hb s F G) := by
  have hpoint := component_card_decomposition (directionSet p S b hb) F
  have hsum := Finset.sum_congr rfl (fun G hG => componentExcess_identity p hb s F G hG hcomp)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    MinimumEquationComponentSets.factors_degree_sum_eq F hF0 hsq, hF.totalDegree hF0] at hsum
  unfold totalExcess
  omega

theorem component_excess_add_intersections_le_total {S : Finset (Geometry.Point p)}
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hG : G ∈ factors F)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    componentExcess p hb s F G + (intersectionPoints (directionSet p S b hb) F).card ≤
      totalExcess p hb s := by
  rw [total_excess_decomposition p hb s F hF hF0 hsq hcomp]
  have hsingle := Finset.single_le_sum (f := fun Q => componentExcess p hb s F Q)
    (fun Q _hQ => Nat.zero_le _) hG
  omega

theorem total_excess_identity {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (hlower : s * (p - s) ≤ (directionSet p S b hb).card) :
    s * (p - s) + totalExcess p hb s = (directionSet p S b hb).card := by
  unfold totalExcess
  omega

theorem total_excess_upper {S : Finset (Geometry.Point p)}
    (hp : 11 ≤ p) (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : PlaneBinaryReduction.InitialDegree
      (RationalPlanePointModel.representatives (DirectionCurveBounds.embedding p)
        (directionSet p S b hb)) s) :
    4 * totalExcess p hb s + p ≤ (p - 2 * s) ^ 2 + 2 := by
  obtain ⟨_hlo, hhi, hkl, _hkn, _hkp, _hF⟩ :=
    DirectionCurveProposition.direction_curve p hp hcard hS hnon hb s hs
  have hk := DirectionCurveBounds.twice_direction_card_le_white p hcard hS hb
  have hn := white_card_upper_bound p hcard hS
  have hdiv := Nat.div_mul_le_self (p * (p - 1)) 2
  have heps := total_excess_identity p hb s hkl
  have hsrem : p - s + s = p := by omega
  have hδrem : p - 2 * s + 2 * s = p := by omega
  have hprem : p - 1 + 1 = p := by omega
  nlinarith

theorem component_excess_polar_bound {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (F G : MvPolynomial (Fin 3) (ZMod p))
    (hG : G ∈ factors F) (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (hs : 2 * s ≤ p) :
    2 * componentExcess p hb s F G ≤ G.totalDegree * (G.totalDegree - (p - 2 * s) - 1) := by
  obtain ⟨H, hGH⟩ := factor_dvd F G hG
  have hdata := hcomp G hG H hGH
  have hupper := hdata.2.2.2.2.2.1
  rw [hdata.1] at hupper
  have hex := componentExcess_identity p hb s F G hG hcomp
  have hebound := hdata.2.2.2.2.2.2
  have hδ : p - 2 * s + 2 * s = p := Nat.sub_add_cancel hs
  have hδe : G.totalDegree - (p - 2 * s) - 1 + (p - 2 * s) + 1 = G.totalDegree := by
    omega
  have hsp : p - s + s = p := by omega
  have hp1 : G.totalDegree + p - 1 + 1 = G.totalDegree + p := by omega
  have hdiv := Nat.div_mul_le_self (G.totalDegree * (G.totalDegree + p - 1)) 2
  nlinarith

end Cylinder.DirectionComponentDecomposition

end
