module

public import Cylinder.ConicRootNormalization

/-! Normal form of an irreducible conic relative to any prescribed line.
The line is sent to Z=0, and the conic becomes a nonzero scalar multiple
of XY-Z² or X²-YZ by an actual invertible linear coordinate change. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicLineNormalForm
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport
open Cylinder.ConicLineCoordinates Cylinder.ConicAffineMaps Cylinder.ConicAffineNormalForms
open Cylinder.ConicRootNormalization Cylinder.ConicTernaryQuadratic

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem exists_conic_line_normal_form (Q ell : PlaneRing K) (hQ : Q.IsHomogeneous 2)
    (hirr : Irreducible Q) (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∃ u : K, u ≠ 0 ∧
      linearPullback g ell = X 2 ∧
      (linearPullback g Q = C u * (X 0 * X 1 - X 2 ^ 2) ∨
        linearPullback g Q = C u * (X 0 ^ 2 - X 1 * X 2)) := by
  obtain ⟨g₀, hg₀⟩ := exists_line_coordinates ell hell hell0
  let P := linearPullback g₀ Q
  have hP : P.IsHomogeneous 2 := linearPullback_homogeneous g₀ Q 2 hQ
  have hPir : Irreducible P := pullback_irreducible g₀ Q hirr
  obtain ⟨a, b, c, d, e, f, hcoeff⟩ := exists_quadratic_coefficients P hP
  change P = sixCoefficients a b c d e f at hcoeff
  rw [hcoeff] at hPir
  obtain ⟨g, u, hu, hg, hnorm⟩ := normalize_coefficients a b c d e f hPir
  refine ⟨g.trans g₀, u, hu, ?_, ?_⟩
  · rw [pullback_trans, hg₀]
    exact pullback_last g hg
  · rw [pullback_trans]
    change linearPullback g P = C u * (X 0 * X 1 - X 2 ^ 2) ∨
      linearPullback g P = C u * (X 0 ^ 2 - X 1 * X 2)
    rw [hcoeff]
    exact hnorm

end Cylinder.ConicLineNormalForm
end
