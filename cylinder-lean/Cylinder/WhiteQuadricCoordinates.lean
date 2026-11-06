module

public import Cylinder.WhiteQuadricResidual
public import Cylinder.NoWhiteQuadric

/-! A quadric on canonical rational coordinate representatives is a genuine
quadric on the original dual point vectors. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WhiteQuadricCoordinates
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.ProjectiveFieldEmbedding Cylinder.LinearEvaluationTransport
open Cylinder.ExactRayMomentsCoordinates Cylinder.NoWhiteQuadric

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K]

theorem coordinate_eval_zero_to_dual (ι : ZMod p →+* K)
    (Q : MvPolynomial (Option (Fin 3)) K) (hQ : Q.IsHomogeneous 2) (H : DualPoint p)
    (hz : eval (vectorMap ι (coordinatePoint p H).rep) Q = 0) :
    eval (vectorMap ι (dualCoordinates p H.rep)) Q = 0 := by
  obtain ⟨u, hu⟩ := exists_coordinate_rep_unit p H
  have hv : vectorMap ι (coordinatePoint p H).rep =
      ι (u : ZMod p) • vectorMap ι (dualCoordinates p H.rep) := by
    rw [← hu, Units.smul_def]
    funext j
    exact ι.map_mul _ _
  rw [hv, homogeneous_eval_smul Q 2 hQ] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (pow_ne_zero 2 (fun h => Units.ne_zero u ((map_eq_zero_iff ι ι.injective).mp h)))

theorem coordinate_quadric_to_original (ι : ZMod p →+* K) {S : Finset (Geometry.Point p)}
    (Q : MvPolynomial (Option (Fin 3)) K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hwhite : ∀ H ∈ whitePoints p S, eval (vectorMap ι (coordinatePoint p H).rep) Q = 0) :
    ∃ Q' : MvPolynomial (Fin 4) K, Q'.IsHomogeneous 2 ∧ Q' ≠ 0 ∧
      ∀ H ∈ whitePoints p S, eval (pointVector p ι H) Q' = 0 := by
  let Q' := rename (finSuccEquiv 3).symm Q
  refine ⟨Q', hQ.rename_isHomogeneous (f := (finSuccEquiv 3).symm), ?_, ?_⟩
  · intro hz
    exact hQ0 ((rename_injective (finSuccEquiv 3).symm (finSuccEquiv 3).symm.injective)
      (by simpa only [Q', map_zero] using hz))
  · intro H hH
    have hz := coordinate_eval_zero_to_dual p ι Q hQ H (hwhite H hH)
    change eval (pointVector p ι H) (rename (finSuccEquiv 3).symm Q) = 0
    rw [eval_rename]
    exact hz

end Cylinder.WhiteQuadricCoordinates
end
