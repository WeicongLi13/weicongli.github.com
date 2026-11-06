module

public import Cylinder.RationalQuadricResidualRays
public import Cylinder.ResidualPointBound
public import Cylinder.ResidualGapArithmetic

/-! The actual residual subset of white dual points is empty. Its upper
bound comes from the literal moment quadric and its lower bound from the
residual-point theorem; neither bound is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.WhiteQuadricResidual
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.ProjectiveFieldEmbedding Cylinder.DirectionCurveBounds
open Cylinder.RationalProjectionRelations Cylinder.RationalQuadricResidual
open Cylinder.RationalQuadricResidualRays Cylinder.EvaluationProjection

variable (p : ℕ) [Fact p.Prime]

def whiteResidual (S : Finset (Geometry.Point p)) (b : DualPoint p) (f g : PlaneRing (CurveField p)) :
    Finset (DualPoint p) :=
  (whitePoints p S).filter (fun H => eval (vectorMap (embedding p) (coordinatePoint p H).rep)
    (originalQuadric (embedding p) (coordinatePoint p b) f g) ≠ 0)

theorem whiteResidual_subset (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (f g : PlaneRing (CurveField p)) : whiteResidual p S b f g ⊆ whitePoints p S :=
  Finset.filter_subset _ _

theorem black_outside_whiteResidual {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (f g : PlaneRing (CurveField p)) : b ∉ whiteResidual p S b f g := by
  intro h
  have hw := whiteResidual_subset p S b f g h
  exact ProjectiveLineCap.white_ne_black p hw hb rfl

theorem whiteResidual_image (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (f g : PlaneRing (CurveField p)) :
    ResidualWhiteProjection.image p (whiteResidual p S b f g) =
      residualSet (embedding p) (whiteImage p S) (coordinatePoint p b) f g := by
  ext P
  constructor
  · intro h
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hHw, hHq⟩ := Finset.mem_filter.mp hH
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨H, hHw, rfl⟩, hHq⟩
  · intro h
    obtain ⟨hP, hPq⟩ := Finset.mem_filter.mp h
    obtain ⟨H, hHw, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_image.mpr ⟨H, Finset.mem_filter.mpr ⟨hHw, hPq⟩, rfl⟩

theorem whiteResidual_card (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (f g : PlaneRing (CurveField p)) :
    (whiteResidual p S b f g).card =
      (residualSet (embedding p) (whiteImage p S) (coordinatePoint p b) f g).card := by
  rw [← whiteResidual_image]
  exact (Finset.card_image_of_injective _ (coordinatePoint_injective p)).symm

theorem white_residual_empty_given_moments {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (f g : PlaneRing (CurveField p))
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (c : ∀ i : BlackProjection.directionSet p S b hb, Fin (BlackProjection.raySize p S b hb i) → CurveField p)
    (hc : ∀ i ν, c i ν ≠ 0)
    (hrel : EvaluationRelation (directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) (BlackProjection.raySize p S b hb)
      (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb)) c (p - 2))
    (hM0 : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) c i 0 = 0)
    (hM2 : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) c i 2 =
      eval (directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i) f * rayMoment _
        (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb)) c i 1)
    (hM3 : ∀ i, rayMoment _ (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb)) c i 3 =
      eval (directionRepresentatives (embedding p) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i) g * rayMoment _
        (rayParameters (embedding p) (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb)) c i 1) :
    whiteResidual p S b f g = ∅ := by
  by_contra hz
  have hZnon : (whiteResidual p S b f g).Nonempty := Finset.nonempty_iff_ne_empty.mpr hz
  let hbZ := black_outside_whiteResidual p hb f g
  have hgeneric := residual_full_support_relation (embedding p) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) f g hf hg c hc (p - 2) (by omega) hrel
  have hfull : ∃ c' : ResidualWhiteProjection.image p (whiteResidual p S b f g) → CurveField p,
      (∀ P, c' P ≠ 0) ∧ PowerEvaluationRelation.Relation
        (fun P : ResidualWhiteProjection.image p (whiteResidual p S b f g) => vectorMap (embedding p) P.val.rep)
        c' (p - 4) := by
    rw [whiteResidual_image p S b f g]
    simpa only [Nat.sub_sub, Nat.reduceAdd] using hgeneric
  obtain ⟨cw, hcw, hrelw⟩ := hfull
  have hthree : ∀ i : ResidualWhiteProjection.directions p (whiteResidual p S b f g) b hbZ,
      3 ≤ ResidualWhiteProjection.raySize p (whiteResidual p S b f g) b hbZ i := by
    have h := residual_rays_ge_three (embedding p) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb) f g hf hg c hc hM0 hM2 hM3
    have htransport : ∀ hOutside : coordinatePoint p b ∉
        ResidualWhiteProjection.image p (whiteResidual p S b f g),
        ∀ i : ProjectiveProjection.directionSet (ZMod p) (Fin 3)
          (ResidualWhiteProjection.image p (whiteResidual p S b f g)) (coordinatePoint p b) hOutside,
          3 ≤ ProjectiveProjection.raySize (ZMod p) (Fin 3)
            (ResidualWhiteProjection.image p (whiteResidual p S b f g)) (coordinatePoint p b) hOutside i := by
      rw [whiteResidual_image p S b f g]
      intro hOutside
      exact h
    exact htransport _
  have hlower := ResidualPointBound.residual_point_bound p hp hcard hS hnon
    (whiteResidual p S b f g) (whiteResidual_subset p S b f g) hZnon b hbZ cw hcw hrelw hthree
  have hupper := residual_card_upper (embedding p) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) f g hf hg c (fun i => two_le_raySize p hcard hS hb i) hc hM0 hM2 hM3
  rw [← whiteResidual_card p S b f g] at hupper
  change (whiteResidual p S b f g).card ≤ 3 * DirectionExcess.rayExcess p S b hb at hupper
  have hexcess := DirectionExcess.ray_excess_upper p hcard hS hnon hb
  rw [SimpleBlackWeights.white_card_exact p hcard hS hnon] at hexcess
  have hbound : 2 * (whiteResidual p S b f g).card ≤
      6 * (1 + p * (p - 1) / 2 - 2 * DirectionExcess.directionLowerBound p) := by
    nlinarith only [hupper, hexcess]
  exact ResidualGapArithmetic.actual_residual_bounds_inconsistent p _ hp hlower hbound

theorem originalQuadric_zero_on_white {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (f g : PlaneRing (CurveField p)) (hempty : whiteResidual p S b f g = ∅) :
    ∀ H ∈ whitePoints p S, eval (vectorMap (embedding p) (coordinatePoint p H).rep)
      (originalQuadric (embedding p) (coordinatePoint p b) f g) = 0 := by
  intro H hH
  by_contra hq
  have hmem : H ∈ whiteResidual p S b f g := Finset.mem_filter.mpr ⟨hH, hq⟩
  rw [hempty] at hmem
  simp at hmem

end Cylinder.WhiteQuadricResidual
end
