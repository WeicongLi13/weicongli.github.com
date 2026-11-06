module

public import Cylinder.ResidualWhiteProjection
public import Cylinder.DirectionCurveBounds

/-! The residual-point lemma from the actual white set, actual rational
projection and actual extension-field full-support relation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ResidualPointBound
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ResidualWhiteProjection Cylinder.RationalPlanePointModel Cylinder.DirectionCurveBounds
open Cylinder.ProjectiveFieldEmbedding Cylinder.ResidualRayArithmetic

variable (p : ℕ) [Fact p.Prime]

/-- The original residual bound, in an equivalent doubled form. Its only
relation hypothesis is the full-support relation in degree p-4 stated in the
manuscript; the minimum ray, direction dependence and point count are derived. -/
theorem residual_point_bound {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Z : Finset (DualPoint p)) (hZ : Z ⊆ whitePoints p S) (hZnon : Z.Nonempty)
    (b : DualPoint p) (hb : b ∉ Z)
    (c : ResidualWhiteProjection.image p Z → CurveField p) (hc : ∀ x, c x ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (fun x : ResidualWhiteProjection.image p Z => vectorMap (embedding p) x.val.rep) c (p - 4))
    (hthree : ∀ i : directions p Z b hb, 3 ≤ ResidualWhiteProjection.raySize p Z b hb i) :
    (p - 5) * (p + 1) ≤ 2 * Z.card := by
  obtain ⟨r, hr, hrhalf, ⟨i, hi⟩, hmin, hcount, hcap⟩ :=
    exists_minimum p hcard hS hnon Z hZ hZnon b hb hthree
  have hdep : ¬EvaluationProjection.Independent
      (representatives (embedding p) (directions p Z b hb)) (p - r - 3) := by
    intro hind
    have hbound := RationalProjectionRelations.ray_lower_bound_of_independent (embedding p)
      (ResidualWhiteProjection.image p Z) (BlackProjection.coordinatePoint p b)
      (outside_image p Z b hb) c hc (p - 4) (p - r - 3) (by omega) hrel hind i
    change p - 4 - (p - r - 3) + 2 ≤ ResidualWhiteProjection.raySize p Z b hb i at hbound
    rw [hi] at hbound
    omega
  have hdir := ResidualDependentDirections.dependent_set_lower p (embedding p) (directions p Z b hb)
    r hr hrhalf hcap hdep
  have hproduct : r * residualThreshold p r * (p - r - residualThreshold p r) ≤ Z.card := by
    have hh := (Nat.mul_le_mul_left r hdir).trans hcount
    simpa only [mul_assoc] using hh
  exact residual_ray_lower_bound p r Z.card hp hr hrhalf hproduct

#print axioms residual_point_bound

end Cylinder.ResidualPointBound
end
