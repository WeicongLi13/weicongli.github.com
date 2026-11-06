module

public import Cylinder.ProjectiveDualityMultiplication
public import Cylinder.LocalResidualRepresentatives

/-! The original residue isomorphisms construct the residual cross identities.
No cross identity between the coefficients is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.LocalResidualCross
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.ProjectivePointIdealTransport Cylinder.ProjectiveIntegerRelations
open Cylinder.ProjectiveCompleteIntersectionDuality Cylinder.ProjectiveDualityMultiplication
open Cylinder.ResidualCoordinateTransport Cylinder.ResidualCoordinateMultiplication

variable {K : Type*} [Field K]

theorem cross_of_residual_representatives (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (j₀ j₁ : ℤ) (n₀ n₁ : ℕ) (htarget : j₁ - n₀ = j₀ - n₁)
    (a₀ : originalRelations c D j₀) (a₁ : originalRelations c D j₁)
    (Q₀ : residualPiece (CompleteIntersectionKoszul.equationsIdeal F G) (originalPointIdeal D)
      (integerPlaneForms K) ((e : ℤ) + t - 3 - j₀))
    (Q₁ : residualPiece (CompleteIntersectionKoszul.equationsIdeal F G) (originalPointIdeal D)
      (integerPlaneForms K) ((e : ℤ) + t - 3 - j₁))
    (hQ₀ : Q₀.val.IsHomogeneous n₀) (hQ₁ : Q₁.val.IsHomogeneous n₁)
    (hclass₀ : projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j₀ a₀ =
      Submodule.Quotient.mk Q₀)
    (hclass₁ : projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j₁ a₁ =
      Submodule.Quotient.mk Q₁) :
    ∀ P : D, eval (c.normalizedPoint P.val) Q₀.val * a₁.val P =
      eval (c.normalizedPoint P.val) Q₁.val * a₀.val P := by
  obtain ⟨j, hj₀, hj₁⟩ : ∃ j : ℤ, j₀ = j + n₁ ∧ j₁ = j + n₀ :=
    ⟨j₁ - n₀, by omega, by omega⟩
  subst j₀
  subst j₁
  let hchart := point_line_ne_zero c F G e t hgood D hpoints
  have hleft := projective_duality_multiply c F G e t he ht hF hG hgood D hpoints
    (j + n₀) n₀ Q₀.val hQ₀ (Submodule.Quotient.mk Q₁)
  have hright := projective_duality_multiply c F G e t he ht hF hG hgood D hpoints
    (j + n₁) n₁ Q₁.val hQ₁ (Submodule.Quotient.mk Q₀)
  rw [← hclass₁, LinearEquiv.symm_apply_apply] at hleft
  rw [← hclass₀, LinearEquiv.symm_apply_apply] at hright
  rw [hclass₁] at hleft
  rw [hclass₀] at hright
  have hleftval := congrArg (fun a => a.val) hleft
  have hrightval := congrArg (fun a => a.val) hright
  have hcoeff : (originalCoefficientMultiplication c D hchart (j + n₀) n₀ Q₀.val hQ₀ a₁).val =
      (originalCoefficientMultiplication c D hchart (j + n₁) n₁ Q₁.val hQ₁ a₀).val := by
    rw [← hleftval, ← hrightval]
    let s := chartValidSystem c F G e t he ht hF hG hgood D hpoints
    change (FullEvaluationDuality.fullEvaluationDuality
      (CurvePolarLocal.dehomogenize (c.coordinates F)) (CurvePolarLocal.dehomogenize (c.coordinates G))
      e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      (fun P : D => c.affinePoint P.val) s.hv s.hfv s.hgv) _ =
      (FullEvaluationDuality.fullEvaluationDuality
      (CurvePolarLocal.dehomogenize (c.coordinates F)) (CurvePolarLocal.dehomogenize (c.coordinates G))
      e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      (fun P : D => c.affinePoint P.val) s.hv s.hfv s.hgv) _
    apply congrArg
    apply Subtype.ext
    change Ideal.Quotient.mk _ (CurvePolarLocal.dehomogenize (c.coordinates (Q₀.val * Q₁.val))) =
      Ideal.Quotient.mk _ (CurvePolarLocal.dehomogenize (c.coordinates (Q₁.val * Q₀.val)))
    rw [mul_comm Q₀.val Q₁.val]
  intro P
  have hv := congrFun hcoeff P
  rw [originalCoefficientMultiplication_apply, originalCoefficientMultiplication_apply] at hv
  simpa only [mul_comm] using hv

end Cylinder.LocalResidualCross
end
