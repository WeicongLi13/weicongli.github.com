module

public import Cylinder.ConicStandardBlocks

/-! The actual conic and prescribed line give standard point blocks by
the constructed normal form. The original secants and matchings are
retained, with no normal form assumed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicBlockNormalForm
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.RationalPlaneLine
open Cylinder.ProjectiveFieldEmbedding Cylinder.LinearEvaluationTransport
open Cylinder.ConicLineNormalForm Cylinder.ConicAffineParametrization
open Cylinder.ConicStandardBlocks Cylinder.BMMArcGeometry

variable {R K : Type*} [Field R] [Field K]

theorem inverse_coordinate_last (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (ell : PlaneRing K) (hell : linearPullback g ell = X 2) (v : Fin 3 → K) :
    g.symm v 2 = eval v ell := by
  have h := congrArg (eval (g.symm v)) hell
  simpa only [linearPullback_eval, LinearEquiv.apply_symm_apply, eval_X] using h.symm

theorem inverse_coordinate_curve (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (Q F : PlaneRing K) (u : K) (hu : u ≠ 0)
    (hQ : linearPullback g Q = C u * F) (v : Fin 3 → K) (hv : eval v Q = 0) :
    eval (g.symm v) F = 0 := by
  have h := congrArg (eval (g.symm v)) hQ
  simp only [linearPullback_eval, LinearEquiv.apply_symm_apply, map_mul, eval_C, hv] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hu

theorem normalized_curve_zero (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint R)
    (F : PlaneRing K) (hF : F.IsHomogeneous 2) (hzero : eval (g (vectorMap ι P.rep)) F = 0) :
    eval (affineRepresentative ι g P) F = 0 := by
  rw [affineRepresentative, homogeneous_eval_smul F 2 hF, hzero, mul_zero]

set_option maxHeartbeats 1000000 in
theorem blocks_from_conic_and_line [IsAlgClosed K] (ι : R →+* K) (X Y D : Finset (PlanePoint R))
    (hdisj : Disjoint X Y) (hX : X.card = D.card) (hY : Y.card = D.card)
    (hcross : ∀ P ∈ X, ∀ Q ∈ Y, ∃ T ∈ D, Collinear P Q T)
    (hmatch : ∀ T : D, ∃ e : X ≃ Y, ∀ P : X, Collinear P.val (e P).val T.val)
    (Q ell : PlaneRing K) (hQ : Q.IsHomogeneous 2) (hirr : Irreducible Q)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hvan : ∀ P ∈ X ∪ Y, eval (vectorMap ι P.rep) Q = 0)
    (hoff : ∀ P ∈ X ∪ Y, eval (vectorMap ι P.rep) ell ≠ 0)
    (hinfty : ∀ T ∈ D, eval (vectorMap ι T.rep) ell = 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K),
      (∀ v, g v 2 = eval v ell) ∧
      ((StandardBlocks ι g (fun x => x⁻¹) X Y D ∧
          ∀ P ∈ X ∪ Y, parameter ι g P ≠ 0) ∨
        StandardBlocks ι g (fun x => x ^ 2) X Y D) := by
  obtain ⟨g, u, hu, hline, hnorm⟩ := exists_conic_line_normal_form Q ell hQ hirr hell hell0
  have hlast := inverse_coordinate_last g ell hline
  have hoff' : ∀ P ∈ X ∪ Y, g.symm (vectorMap ι P.rep) 2 ≠ 0 := by
    intro P hP
    rw [hlast]
    exact hoff P hP
  have hinfty' : ∀ T ∈ D, g.symm (vectorMap ι T.rep) 2 = 0 := by
    intro T hT
    rw [hlast]
    exact hinfty T hT
  refine ⟨g.symm, hlast, ?_⟩
  rcases hnorm with hnorm | hnorm
  · have hF : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2 : PlaneRing K).IsHomogeneous 2 := by
      have hprod : (MvPolynomial.X 0 * MvPolynomial.X 1 : PlaneRing K).IsHomogeneous 2 := by
        simpa only [Nat.reduceAdd] using (isHomogeneous_X K 0).mul (isHomogeneous_X K 1)
      exact hprod.sub (isHomogeneous_X_pow 2 2)
    have hshape : ∀ P ∈ X ∪ Y, parameter ι g.symm P ≠ 0 ∧
        affineRepresentative ι g.symm P = ![parameter ι g.symm P, (parameter ι g.symm P)⁻¹, 1] := by
      intro P hP
      exact hyperbola_vector _ (affineRepresentative_last ι g.symm P (hoff' P hP))
        (normalized_curve_zero ι g.symm P _ hF
          (inverse_coordinate_curve g Q _ u hu hnorm _ (hvan P hP)))
    exact Or.inl ⟨⟨hdisj, hX, hY, hoff', hinfty', fun P hP => (hshape P hP).2, hcross, hmatch⟩,
      fun P hP => (hshape P hP).1⟩
  · have hF : (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 * MvPolynomial.X 2 : PlaneRing K).IsHomogeneous 2 := by
      exact (isHomogeneous_X_pow 0 2).sub
        (by simpa only [Nat.reduceAdd] using (isHomogeneous_X K 1).mul (isHomogeneous_X K 2))
    have hshape : ∀ P ∈ X ∪ Y,
        affineRepresentative ι g.symm P = ![parameter ι g.symm P, (parameter ι g.symm P) ^ 2, 1] := by
      intro P hP
      exact parabola_vector _ (affineRepresentative_last ι g.symm P (hoff' P hP))
        (normalized_curve_zero ι g.symm P _ hF
          (inverse_coordinate_curve g Q _ u hu hnorm _ (hvan P hP)))
    exact Or.inr ⟨hdisj, hX, hY, hoff', hinfty', hshape, hcross, hmatch⟩

end Cylinder.ConicBlockNormalForm
end
