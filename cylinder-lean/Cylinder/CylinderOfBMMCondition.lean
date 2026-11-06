module

public import Cylinder.WhiteQuadricLift
public import Cylinder.NoWhiteQuadricCondition

/-! The completed cylinder argument with its one remaining geometric
classification input stated explicitly. BMMClassification is not proved here. -/

@[expose] public section
noncomputable section

namespace Cylinder.CylinderOfBMMCondition

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.WhitePlaneHyperfocus Cylinder.WhitePlaneBMMCondition
open Cylinder.DirectionCurveBounds Cylinder.ProjectiveFieldEmbedding

variable (p : ℕ) [Fact p.Prime]

theorem white_isArc_of_noncylinder {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) :
    IsArc p S := by
  by_contra hnotarc
  obtain ⟨b, hb⟩ := black_nonempty p hcard hS
  obtain ⟨Q, hQ, hQ0, hvan⟩ := WhiteQuadricLift.white_quadric_lift p hp hcard hS hnon hb
  exact NoWhiteQuadric.no_quadric_of_not_isArc p hp hcard hS hnon hnotarc Q hQ hQ0 hvan

theorem strongCylinderConjecture_of_bmm (hp : 11 ≤ p) (hBMM : BMMClassification p) :
    Geometry.StrongCylinderConjecture p := by
  intro S hcard hS
  by_contra hnon
  exact (WhiteNotCapCondition.white_not_isArc_of_bmm p hBMM hp hcard hS hnon)
    (white_isArc_of_noncylinder p hp hcard hS hnon)

end Cylinder.CylinderOfBMMCondition

end
