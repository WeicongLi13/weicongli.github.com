module

public import Cylinder.BMMTheorem
public import Cylinder.NoWhiteQuadricCondition

/-! The white-point consequences with the classification condition
discharged by the fully proved BMM theorem. -/

@[expose] public section
noncomputable section

namespace Cylinder.FinalConsequences

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.DualLineBalance Cylinder.WhitePlaneHyperfocus Cylinder.NoWhiteQuadric

variable (p : ℕ) [Fact p.Prime]

theorem white_not_isArc {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) : ¬IsArc p S :=
  WhiteNotCapCondition.white_not_isArc_of_bmm p (BMMTheorem.bmm_classification p)
    hp hcard hS hnon

theorem exists_three_collinear_white {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) :
    ∃ L : Submodule (ZMod p) (DualSpace p), Module.finrank (ZMod p) L = 2 ∧
      ∃ a b c : DualPoint p, a ∈ whiteSlice p S L ∧ b ∈ whiteSlice p S L ∧
        c ∈ whiteSlice p S L ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  WhiteNotCapCondition.exists_three_collinear_white_of_bmm p (BMMTheorem.bmm_classification p)
    hp hcard hS hnon

theorem quadric_vanishing_implies_zero {K : Type*} [Field K] [Infinite K]
    [Algebra (ZMod p) K] {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2)
    (hwhite : ∀ H ∈ whitePoints p S, eval (pointVector p (algebraMap (ZMod p) K) H) Q = 0) :
    Q = 0 :=
  NoWhiteQuadricCondition.quadric_vanishing_implies_zero_of_bmm p
    (BMMTheorem.bmm_classification p) hp hcard hS hnon Q hQ hwhite

end Cylinder.FinalConsequences

end
