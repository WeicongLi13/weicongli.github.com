module

public import Cylinder.DirectionCurveComponentBounds
public import Cylinder.MinimumEquationComponentSets
public import Cylinder.ExactRayMomentsTheorem

/-! The direction-curve proposition with the actual first moment supplied. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.DirectionCurveProposition

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.DirectionCurveBounds

variable (p : ℕ) [Fact p.Prime]

theorem full_support_direction_relation {S : Finset (Geometry.Point p)} (hp : 3 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ u : directionSet p S b hb → CurveField p,
      (∀ i, u i ≠ 0) ∧ PowerEvaluationRelation.Relation
        (representatives (embedding p) (directionSet p S b hb)) u (p - 3) := by
  obtain ⟨u, hu, hrel⟩ := ExactRayMomentsTheorem.weight_one_full_support_direction_relation
    p (K := CurveField p) hp hcard hS hb
    (SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb)
  have hemb : embedding p = ProductEvaluationRelation.primeEmbedding p (K := CurveField p) :=
    Subsingleton.elim _ _
  have hreps : representatives (embedding p) (directionSet p S b hb) =
      BlackProjectionVandermonde.directionRepresentatives p (K := CurveField p) hb := by
    funext i j
    exact congrArg (fun f : ZMod p →+* CurveField p => f (i.val.rep j)) hemb
  refine ⟨u, hu, ?_⟩
  rw [hreps]
  exact hrel

theorem direction_curve {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (whitePoints p S).card / 2 ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 ∧
      ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
        (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧ Squarefree F ∧
        Squarefree (MvPolynomial.map (embedding p) F) ∧
        (∀ G ∈ PlaneCurveFactors.factors F,
          Irreducible (MvPolynomial.map (embedding p) G)) ∧
        ∀ G ∈ PlaneCurveFactors.factors F, p - 2 * s + 1 ≤ G.totalDegree := by
  obtain ⟨u, hu, hrel⟩ := full_support_direction_relation p (by omega) hcard hS hnon hb
  exact DirectionCurveComponentBounds.direction_curve_bounds p hp hcard hS hnon hb s hs u hu hrel

/-- The component assertions refer to the literal set of directions on one
component and on no other component. The cofactor description and its
full-support relation are included for subsequent interpolation arguments. -/
def ComponentConclusion (s : ℕ) (D : Finset (RationalPlaneLine.PlanePoint (ZMod p)))
    (F : MvPolynomial (Fin 3) (ZMod p)) : Prop :=
  ∀ G ∈ PlaneCurveFactors.factors F, ∀ H : MvPolynomial (Fin 3) (ZMod p), F = G * H →
    MinimumEquationComponents.exclusivePoints D H =
      MinimumEquationComponentSets.componentPoints D F G ∧
    (MinimumEquationComponents.exclusivePoints D H).Nonempty ∧
    InitialDegree (representatives (embedding p)
      (MinimumEquationComponents.exclusivePoints D H)) G.totalDegree ∧
    (∃ c : MinimumEquationComponents.exclusivePoints D H → CurveField p,
      (∀ i, c i ≠ 0) ∧ PowerEvaluationRelation.Relation
        (representatives (embedding p) (MinimumEquationComponents.exclusivePoints D H))
        c (p - 3 - s + G.totalDegree)) ∧
    G.totalDegree * (p - s) ≤ (MinimumEquationComponents.exclusivePoints D H).card ∧
    (MinimumEquationComponents.exclusivePoints D H).card ≤
      G.totalDegree * (G.totalDegree + p - 1) / 2 ∧
    p - 2 * s + 1 ≤ G.totalDegree

theorem direction_curve_with_components {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (whitePoints p S).card / 2 ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 ∧
      ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
        (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧ Squarefree F ∧
        Squarefree (MvPolynomial.map (embedding p) F) ∧
        (∀ G ∈ PlaneCurveFactors.factors F,
          Irreducible (MvPolynomial.map (embedding p) G)) ∧
        (∑ G ∈ PlaneCurveFactors.factors F, G.totalDegree) = s ∧
        ComponentConclusion p s (directionSet p S b hb) F := by
  obtain ⟨u, hu, hrel⟩ := full_support_direction_relation p (by omega) hcard hS hnon hb
  obtain ⟨hlo, hhi, hkl, hkn, hkp⟩ :=
    DirectionCurveBounds.numerical_bounds p hp hcard hS hnon hb s hs u hu hrel
  obtain ⟨F, hF, hF0, hzero, hsq, hsqmap, habs⟩ :=
    MinimumEquationAbsoluteFactors.exists_reduced_base_equation_with_absolute_factors
      p (directionSet p S b hb) s hs
  refine ⟨hlo, hhi, hkl, hkn, hkp, F, hF, hF0, hzero, hsq, hsqmap, habs, ?_, ?_⟩
  · rw [MinimumEquationComponentSets.factors_degree_sum_eq F hF0 hsq, hF.totalDegree hF0]
  · intro G hG H hGH
    exact ⟨MinimumEquationComponentSets.exclusivePoints_eq_componentPoints
      (directionSet p S b hb) F G H hF0 hsq hG hGH hzero,
      DirectionCurveComponentBounds.component_bounds p hp hcard hS hnon hb s hs u hu hrel
        F hF hF0 hzero G (PlaneCurveFactors.factor_irreducible F G hG) H hGH⟩

/-- An initial degree exists for the actual direction set. No curve or
first-moment relation is required as an additional assumption. -/
theorem exists_direction_curve {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ s : ℕ, InitialDegree (representatives (embedding p) (directionSet p S b hb)) s ∧
      DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (whitePoints p S).card / 2 ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 ∧
      ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
        (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧ Squarefree F ∧
        Squarefree (MvPolynomial.map (embedding p) F) ∧
        (∀ G ∈ PlaneCurveFactors.factors F,
          Irreducible (MvPolynomial.map (embedding p) G)) ∧
        (∑ G ∈ PlaneCurveFactors.factors F, G.totalDegree) = s ∧
        ComponentConclusion p s (directionSet p S b hb) F := by
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree
    (representatives (embedding p) (directionSet p S b hb))
  exact ⟨s, hs, direction_curve_with_components p hp hcard hS hnon hb s hs⟩

end Cylinder.DirectionCurveProposition

end
