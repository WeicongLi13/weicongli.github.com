module

public import Cylinder.ComponentMomentRelations
public import Cylinder.LocalCurveFamily
public import Cylinder.ComponentTwoPointSubset
public import Cylinder.ComponentInterpolationArithmetic
public import Cylinder.DirectionComponentDecomposition

/-! Actual component interpolation with one fixed family of actual product
residues. Numerical character and two-point-ray estimates are all derived. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ComponentInterpolation
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ExactRayMomentsTheorem Cylinder.BlackProjectionVandermonde
open Cylinder.RationalPlanePointModel Cylinder.MinimumEquationComponents
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition Cylinder.PlaneCurveFactors
open Cylinder.ComponentMomentRelations Cylinder.EvaluationProjection
open Cylinder.HilbertCharacterFormulas Cylinder.ComponentCharacterNumeric
open Cylinder.MinimumEquationComponentSets Cylinder.DirectionCurveComponentCounting
open Cylinder.ManyTwoCharacter Cylinder.DirectionComponentDecomposition

variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ZMod p) := Classical.decEq _

set_option maxHeartbeats 800000 in
theorem component_interpolation_given_residues {S : Finset (Geometry.Point p)}
    (hp : 11 ≤ p) (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F G H : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hsq : Squarefree F) (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (hG : G ∈ factors F) (hGirr : Irreducible (MvPolynomial.map (embedding p) G))
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) (hGH : F = G * H)
    (c : DualPoint p → ZMod p)
    (hc : ∀ i ν, rayResiduesOverField p (K := CurveField p) hb c i ν ≠ 0)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb) (raySize p S b hb)
      (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (hM0 : ∀ i, rawMoment p hb c i 0 = 0) (hM1 : ∀ i, rawMoment p hb c i 1 ≠ 0) :
    ∃ f g : PlaneRing (CurveField p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P : exclusivePoints (directionSet p S b hb) H,
        rawMoment p hb c (componentIndex p hb H P) 2 =
          eval (representatives (embedding p) (exclusivePoints (directionSet p S b hb) H) P) f *
            rawMoment p hb c (componentIndex p hb H P) 1) ∧
      (∀ P : exclusivePoints (directionSet p S b hb) H,
        rawMoment p hb c (componentIndex p hb H P) 3 =
          eval (representatives (embedding p) (exclusivePoints (directionSet p S b hb) H) P) g *
            rawMoment p hb c (componentIndex p hb H P) 1) := by
  let D := directionSet p S b hb
  let E := exclusivePoints D H
  let e := G.totalDegree
  let d := p - 3 - s + e
  let v := representatives (embedding p) E
  let μ := componentMoment p hb H c
  have hdata := hcomp G hG H hGH
  have hEnon : E.Nonempty := hdata.2.1
  let : Nonempty E := hEnon.coe_sort
  have hinit : InitialDegree v e := hdata.2.2.1
  have heq : E = componentPoints D F G := hdata.1
  have hcurve := direction_curve p hp hcard hS hnon hb s hs
  have hsupper : s ≤ (p - 3) / 2 := hcurve.2.1
  have hGbase := factor_irreducible F G hG
  obtain ⟨_hH0, hGhom, _hHhom, hdegree, _hGpos⟩ := cofactor_data D s F hF hF0 G hGbase H hGH
  have hes : e ≤ s := by dsimp only [e]; omega
  have hδe : p - 2 * s + 1 ≤ e := hdata.2.2.2.2.2.2
  have he4 : 4 ≤ e := by omega
  have hd : 2 * e ≤ d := (component_degree_arithmetic p s e (by omega) hsupper hes).1
  have hv : ∀ P : E, v P ≠ 0 := representatives_nonzero (embedding p) E
  have hsep : ProjectivelyDistinct v := representatives_distinct (embedding p) E
  have hGzero : ∀ P : E, eval (v P) (MvPolynomial.map (embedding p) G) = 0 := by
    intro P
    rw [eval_mapped_cofactor, factor_zero_on_exclusive D F G H hGH hzero P.val P.property, map_zero]
  have hμ0 : ∀ P : E, μ 0 P ≠ 0 := by
    intro P
    exact mul_ne_zero (componentWeight_ne_zero p hb H P) (hM1 (componentIndex p hb H P))
  have hμrel : ∀ q ≤ d, PowerEvaluationRelation.Relation v (μ q) (d - q) := by
    intro q hq
    exact component_moment_relation p hb c hrel s hsupper F G H hF hF0 hGbase hGH q hq
  have hurel : PowerEvaluationRelation.Relation v (μ 0) d := by
    simpa only [Nat.sub_zero] using hμrel 0 (by omega)
  have hcharacter := ActualComponentCharacter.character_increments v hv hsep (MvPolynomial.map (embedding p) G)
    e (hGhom.map _) hGirr hGzero hinit (μ 0) hμ0 d hd hurel
  have hconn := hcharacter.1
  have hincsum := component_increment_data p hb (by omega) s hsupper F G hF hF0 hG hGirr hcomp
  let B := componentIncrement p hb s F G
  let ell := componentExcess p hb s F G
  let δ := p - 2 * s
  have hB : increment (numericalCharacter v) d = B := by
    funext j
    change increment (numericalCharacter (representatives (embedding p) E)) d j = _
    rw [heq]
    rfl
  have hδ : 3 ≤ δ := by dsimp only [δ]; omega
  have hpeq : p = 2 * s + δ := by dsimp only [δ]; omega
  have hExcess := total_excess_upper p hp hcard hS hnon hb s hs
  have hcomponent := component_excess_add_intersections_le_total p hb s F G hF hF0 hsq hG hcomp
  have hExcess' : 4 * ell + p ≤ δ ^ 2 + 2 := by dsimp only [ell, δ]; omega
  have hPolar : 2 * ell ≤ e * (e - δ - 1) :=
    component_excess_polar_bound p hb s F G hG hcomp (by omega)
  have hcases := ComponentInterpolationArithmetic.zero_third_or_plateau B p s e δ ell he4 hδ hes
    (by dsimp only [δ]; omega) hpeq hExcess' hPolar hincsum.1 hincsum.2
  have hforms : ∃ f g : PlaneRing (CurveField p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P : E, μ 1 P = eval (v P) f * μ 0 P) ∧
      (∀ P : E, μ 2 P = eval (v P) g * μ 0 P) := by
    rcases hcases with hb3 | ⟨m, hm, hsmall, hstair, hplateau⟩
    · apply ActualComponentCharacter.zero_third_forms v hv hsep (MvPolynomial.map (embedding p) G)
        e he4 (hGhom.map _) hGirr hGzero hinit (μ 0) hμ0 d hd hurel _ (μ 1) (μ 2)
        (hμrel 1 (by omega)) (hμrel 2 (by omega))
      simpa only [hB] using hb3
    · let T := ComponentTwoPointSubset.twoPointSubset p hb H
      have hTcard := ComponentTwoPointSubset.twoPointSubset_card_gt p hp hcard hS hnon hb s hs
        F G H hF hF0 hsq hG hGirr hcomp hGH m hm hsmall hstair
      have hplateau' : ∀ r < 4, increment (numericalCharacter v) d (3 * m + r) = m := by
        simpa only [hB] using hplateau
      apply LocalCurveFamily.local_curve_interpolation v hv hsep (MvPolynomial.map (embedding p) G)
        e d m (hGhom.map _) hGirr hinit hGzero (by omega) hsmall hd
        (μ 0) hμ0 μ rfl (fun q hq => hμrel q (by omega)) hconn hplateau' T hTcard
      intro P hP q hq
      have hr : raySize p S b hb (componentIndex p hb H P) = 2 := by
        exact (Finset.mem_filter.mp hP).2
      exact component_two_ray_recurrence p hb H c hc hM0 P hr q
  obtain ⟨f, g, hf, hg, hfirst, hsecond⟩ := hforms
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · intro P
    apply mul_left_cancel₀ (componentWeight_ne_zero p hb H P)
    calc
      componentWeight p hb H P * rawMoment p hb c (componentIndex p hb H P) 2 =
        eval (v P) f * (componentWeight p hb H P * rawMoment p hb c (componentIndex p hb H P) 1) := hfirst P
      _ = _ := by ring
  · intro P
    apply mul_left_cancel₀ (componentWeight_ne_zero p hb H P)
    calc
      componentWeight p hb H P * rawMoment p hb c (componentIndex p hb H P) 3 =
        eval (v P) g * (componentWeight p hb H P * rawMoment p hb c (componentIndex p hb H P) 1) := hsecond P
      _ = _ := by ring

#print axioms component_interpolation_given_residues

end Cylinder.ComponentInterpolation
end
