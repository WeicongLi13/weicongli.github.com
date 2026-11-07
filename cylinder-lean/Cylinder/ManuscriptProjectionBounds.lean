module

public import Cylinder.ProjectionTransport
public import Cylinder.ProjectionTransportFields
public import Cylinder.ProjectionTransportGeometry
public import Cylinder.DirectionExcess
public import Cylinder.ManuscriptCurveComponents
public import Cylinder.FinalExceptionalDirections

/-! The actual direction and ray counts for every choice of projection chart.
The same chart is used throughout; the geometric hyperplane interpretation
is supplied by `ArbitraryProjectionHyperplane`. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ManuscriptProjectionBounds
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ProjectionChart Cylinder.DirectionCurveBounds Cylinder.RationalPlanePointModel

variable (p : ℕ) [Fact p.Prime]

abbrev ProjectionChart (b : DualPoint p) := Chart (coordinatePoint p b)

abbrev directions (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :=
  ProjectionTransport.directionSet (whiteImage p S) (black_outside_whiteImage p hb) C

abbrev raySize (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :=
  ProjectionTransport.raySize (whiteImage p S) (black_outside_whiteImage p hb) C

abbrev indexEquiv (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :=
  ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C

theorem raySize_eq (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) (i : directionSet p S b hb) :
    raySize p S b hb C (indexEquiv p S b hb C i) = BlackProjection.raySize p S b hb i :=
  ProjectionTransport.raySize_eq (whiteImage p S) (black_outside_whiteImage p hb) C i

theorem directions_card (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :
    (directions p S b hb C).card = (directionSet p S b hb).card :=
  ProjectionTransport.directionSet_card (whiteImage p S) (black_outside_whiteImage p hb) C

def rayExcess (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) : ℕ :=
  ∑ i : directions p S b hb C, (raySize p S b hb C i - 2)

def largeRays (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) : Finset (directions p S b hb C) :=
  Finset.univ.filter (fun i => 3 ≤ raySize p S b hb C i)

theorem rayExcess_eq (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :
    rayExcess p S b hb C = DirectionExcess.rayExcess p S b hb := by
  unfold rayExcess DirectionExcess.rayExcess
  rw [← (indexEquiv p S b hb C).sum_comp]
  simp only [raySize_eq]

def largeIndexEquiv (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :
    DirectionExcess.largeRays p S b hb ≃ largeRays p S b hb C where
  toFun i := ⟨indexEquiv p S b hb C i.val, by
    simpa only [largeRays, DirectionExcess.largeRays, Finset.mem_filter,
      Finset.mem_univ, true_and, raySize_eq] using i.property⟩
  invFun j := ⟨(indexEquiv p S b hb C).symm j.val, by
    have h := j.property
    have hr := raySize_eq p S b hb C ((indexEquiv p S b hb C).symm j.val)
    simp only [Equiv.apply_symm_apply] at hr
    simpa only [largeRays, DirectionExcess.largeRays, Finset.mem_filter,
      Finset.mem_univ, true_and, hr] using h⟩
  left_inv i := Subtype.ext ((indexEquiv p S b hb C).symm_apply_apply i.val)
  right_inv j := Subtype.ext ((indexEquiv p S b hb C).apply_symm_apply j.val)

theorem largeRays_card (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :
    (largeRays p S b hb C).card = (DirectionExcess.largeRays p S b hb).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (largeIndexEquiv p S b hb C).symm

theorem white_card_paper {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) :
    (whitePoints p S).card = (p ^ 2 - p + 2) / 2 := by
  rw [SimpleBlackWeights.white_card_exact p hcard hS hnon]
  have he : p ^ 2 - p = p * (p - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [he, Nat.add_div_right] <;> omega

/-- Corollary 4.11 for the given projection chart, with the paper's exact
white-set cardinality substituted, not left as an additional parameter. -/
theorem excess {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (C : ProjectionChart p b) :
    rayExcess p S b hb C = (p ^ 2 - p + 2) / 2 - 2 * (directions p S b hb C).card ∧
    (largeRays p S b hb C).card ≤ (p ^ 2 - p + 2) / 2 - 2 * (directions p S b hb C).card := by
  have hwhite := white_card_paper p hcard hS hnon
  have he := DirectionExcess.ray_excess_identity p hcard hS hb
  rw [hwhite] at he
  constructor
  · rw [rayExcess_eq, directions_card]
    exact he
  · rw [largeRays_card, directions_card, ← he]
    exact DirectionExcess.large_rays_card_le_excess p hb

/-- Proposition 4.12, with the least degree and cardinality of the prescribed
projection, and with no transport or full-support hypothesis added. -/
theorem window {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (C : ProjectionChart p b) (s : ℕ)
    (hs : PlaneBinaryReduction.InitialDegree
      (representatives (embedding p) (directions p S b hb C)) s) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
    s * (p - s) ≤ (directions p S b hb C).card ∧
    (directions p S b hb C).card ≤ (p ^ 2 - p + 2) / 4 ∧
    (directions p S b hb C).card ≤ s * (s + p - 1) / 2 := by
  have hs₀ := (ProjectionTransportFields.initialDegree_mapped_directionSet
    (whiteImage p S) (black_outside_whiteImage p hb) (embedding p) C s).mp hs
  obtain ⟨hlo, hhi, hkl, hkn, hkp, _⟩ :=
    DirectionCurveProposition.direction_curve p hp hcard hS hnon hb s hs₀
  rw [white_card_paper p hcard hS hnon, Nat.div_div_eq_div_mul] at hkn
  simpa only [directions_card, show 2 * 2 = 4 from rfl] using
    (show DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (p ^ 2 - p + 2) / (2 * 2) ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 from ⟨hlo, hhi, hkl, hkn, hkp⟩)

/-- Lemma 4.13 applies to the actual prescribed minimum equation `F` in the
given projection chart, including its literal exclusive component sets. -/
theorem components {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (C : ProjectionChart p b) (s : ℕ)
    (hs : PlaneBinaryReduction.InitialDegree
      (representatives (embedding p) (directions p S b hb C)) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ directions p S b hb C, MvPolynomial.eval P.rep F = 0) :
    Squarefree F ∧ Squarefree (MvPolynomial.map (embedding p) F) ∧
    (∀ G ∈ PlaneCurveFactors.factors F, Irreducible (MvPolynomial.map (embedding p) G)) ∧
    (∑ G ∈ PlaneCurveFactors.factors F, G.totalDegree) = s ∧
    DirectionCurveProposition.ComponentConclusion p s (directions p S b hb C) F := by
  have hcap := ProjectionTransportGeometry.lineCap_image C.directionEquiv
    (directionSet p S b hb) ((p - 1) / 2) (direction_lineCap p hcard hS hnon hb)
  obtain ⟨u, hu, hrel⟩ := ProjectionTransportFields.full_support_mapped_directionSet
    (whiteImage p S) (black_outside_whiteImage p hb) (embedding p) C (p - 3)
    (DirectionCurveProposition.full_support_direction_relation p (by omega) hcard hS hnon hb)
  exact ManuscriptCurveComponents.given_minimum_equation p hp (directions p S b hb C)
    hcap s hs u hu hrel (window p hp hcard hS hnon hb C s hs).2.1 F hF hF0 hzero

end Cylinder.ManuscriptProjectionBounds
end
