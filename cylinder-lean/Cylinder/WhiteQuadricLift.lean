module

public import Cylinder.WhiteQuadricCoordinates
public import Cylinder.GlobalMomentsResidualData

/-! The original quadric lifting proposition. All moment and residual
properties are obtained from the original p-divisible configuration. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WhiteQuadricLift
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ProjectiveFieldEmbedding Cylinder.DirectionCurveBounds Cylinder.HilbertEvaluation
open Cylinder.EvaluationProjection Cylinder.ExactRayMomentsTheorem
open Cylinder.GlobalMomentResidues Cylinder.RationalProjectionRelations
open Cylinder.RationalQuadricResidual Cylinder.WhiteQuadricResidual

variable (p : ℕ) [Fact p.Prime]

/-- Proposition `prop:lift`: the actual white dual points lie on a nonzero
homogeneous quadric over the algebraic closure. No relation, moment form,
residual support, ray bound or point count is an extra hypothesis. -/
theorem white_quadric_lift {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ Q : MvPolynomial (Fin 4) (CurveField p), Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧
      ∀ H ∈ whitePoints p S, eval (NoWhiteQuadric.pointVector p (embedding p) H) Q = 0 := by
  obtain ⟨c, f, g, hf, hg, hc, hrel, hM0, _hM1, hM2, hM3⟩ :=
    GlobalMomentsResidualData.exists_actual_global_residue_data p hp hcard hS hnon hb
  have ha : BlackProjectionVandermonde.directionRepresentatives p (K := CurveField p) hb =
      directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) := by
    funext i j
    exact congrArg (fun ι : ZMod p →+* CurveField p => ι (i.val.rep j))
      (Subsingleton.elim (ProductEvaluationRelation.primeEmbedding p) (embedding p))
  have ht : BlackProjectionVandermonde.rayTimesOverField p (K := CurveField p) hb =
      rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) := by
    funext i ν
    exact congrArg (fun ι : ZMod p →+* CurveField p => ι
      (ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i ν))
      (Subsingleton.elim (ProductEvaluationRelation.primeEmbedding p) (embedding p))
  rw [ha, ht] at hrel
  have hv : RationalPlanePointModel.representatives (embedding p) (BlackProjection.directionSet p S b hb) =
      directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) := by
    funext i j
    rfl
  rw [hv] at hM2 hM3
  have hzero : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) (rayResiduesOverField p hb c) i 0 = 0 := by
    simpa only [actualMoment, ht] using hM0
  have htwo : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) (rayResiduesOverField p hb c) i 2 =
      eval (directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i) f * rayMoment _
        (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb)) (rayResiduesOverField p hb c) i 1 := by
    simpa only [actualMoment, ht] using hM2
  have hthree : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) (rayResiduesOverField p hb c) i 3 =
      eval (directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i) g * rayMoment _
        (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb)) (rayResiduesOverField p hb c) i 1 := by
    simpa only [actualMoment, ht] using hM3
  have hempty := white_residual_empty_given_moments p hp hcard hS hnon hb f g hf hg
    (rayResiduesOverField p hb c) hc hrel hzero htwo hthree
  exact WhiteQuadricCoordinates.coordinate_quadric_to_original p (embedding p)
    (originalQuadric (embedding p) (coordinatePoint p b) f g)
    (originalQuadric_homogeneous (embedding p) (coordinatePoint p b) f g hf hg)
    (originalQuadric_nonzero (embedding p) (coordinatePoint p b) f g hf hg)
    (originalQuadric_zero_on_white p f g hempty)

end Cylinder.WhiteQuadricLift
end
