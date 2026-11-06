module

public import Cylinder.BMMClassificationCounting

/-! Exchanging the last two actual white endpoints exchanges the two
black axes and preserves the literal unordered white-pair key. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMOrientedAxes

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BMMFourTupleBlackGeometry Cylinder.BMMThreeSecantConfigurations
open Cylinder.BMMClassificationCounting Cylinder.ProjectiveSecantCounting

variable {K : Type*} [Field K]

theorem swapLast_firstLine (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) : firstLine N (swapLast N T) = secondLine N T := rfl

theorem swapLast_secondLine (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) : secondLine N (swapLast N T) = firstLine N T := rfl

theorem swapLast_fourTupleKey (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) : fourTupleKey N R (swapLast N T) = fourTupleKey N R T := by
  change ({{T.P.val, T.Q.val}, {T.V.val, T.U.val}} : Finset (Finset (PlanePoint K))) =
    {{T.P.val, T.Q.val}, {T.U.val, T.V.val}}
  rw [Finset.pair_comm T.V.val T.U.val]

theorem exists_oriented_axes (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (ell m : PlaneLine K) (haxes : HasAxes N T ell m) :
    ∃ U : FourTuple (configuration N) N.E R,
      firstLine N U = ell ∧ secondLine N U = m ∧ fourTupleKey N R U = fourTupleKey N R T := by
  rcases haxes with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact ⟨T, hfirst, hsecond, rfl⟩
  · exact ⟨swapLast N T, (swapLast_firstLine N T).trans hsecond,
      (swapLast_secondLine N T).trans hfirst, swapLast_fourTupleKey N T⟩

end Cylinder.BMMOrientedAxes

end
