module

public import Cylinder.NoWhiteQuadric
public import Cylinder.WhiteNotCapCondition

/-! The original white-quadric exclusion with the sole unproved external
classification kept visible as the hypothesis `BMMClassification`. -/

@[expose] public section
noncomputable section

namespace Cylinder.NoWhiteQuadricCondition

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.WhitePlaneBMMCondition Cylinder.NoWhiteQuadric

variable (p : ℕ) [Fact p.Prime]

theorem quadric_vanishing_implies_zero_of_bmm {K : Type*} [Field K] [Infinite K]
    [Algebra (ZMod p) K] (hBMM : BMMClassification p) {S : Finset (Geometry.Point p)}
    (hp : 11 ≤ p) (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2)
    (hwhite : ∀ H ∈ whitePoints p S, eval (pointVector p (algebraMap (ZMod p) K) H) Q = 0) : Q = 0 := by
  by_contra hQ0
  exact no_quadric_of_not_isArc p hp hcard hS hnon
    (WhiteNotCapCondition.white_not_isArc_of_bmm p hBMM hp hcard hS hnon) Q hQ hQ0 hwhite

end Cylinder.NoWhiteQuadricCondition

end
