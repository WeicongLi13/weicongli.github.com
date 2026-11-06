module

public import Cylinder.ConicAffineParametrization

/-! Actual secants of the normalized conic have their genuine affine
slopes. A point at infinity on such a secant has nonzero first coordinate,
and distinct rational infinity points have distinct slopes. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ConicAffineDirections
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct
open Cylinder.ProjectiveFieldEmbedding Cylinder.ConicAffineParametrization Cylinder.BMMArcGeometry

variable {R K : Type*} [Field R] [Field K]

theorem dot_cross_smul (a b : K) (v w z : Fin 3 → K) :
    dot (cross (a • v) (b • w)) z = a * b * dot (cross v w) z := by
  simp [dot, cross, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

theorem affine_collinear (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q T : PlanePoint R) (hPQ : P ≠ Q) (hcol : Collinear P Q T) :
    dot (cross (affineRepresentative ι g P) (affineRepresentative ι g Q))
      (g (vectorMap ι T.rep)) = 0 := by
  rw [affineRepresentative, affineRepresentative, dot_cross_smul,
    collinear_after_field_coordinates ι g P Q T hPQ hcol, mul_zero]

def directionSlope (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (T : PlanePoint R) : K :=
  g (vectorMap ι T.rep) 1 / g (vectorMap ι T.rep) 0

theorem secant_direction_slope (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q T : PlanePoint R) (hPQ : P ≠ Q) (hcol : Collinear P Q T)
    (hP : g (vectorMap ι P.rep) 2 ≠ 0) (hQ : g (vectorMap ι Q.rep) 2 ≠ 0)
    (hT : g (vectorMap ι T.rep) 2 = 0)
    (hdiff : affineRepresentative ι g P 0 ≠ affineRepresentative ι g Q 0) :
    g (vectorMap ι T.rep) 0 ≠ 0 ∧ directionSlope ι g T =
      (affineRepresentative ι g Q 1 - affineRepresentative ι g P 1) /
        (affineRepresentative ι g Q 0 - affineRepresentative ι g P 0) := by
  have hcol' := affine_collinear ι g P Q T hPQ hcol
  have hlastP := affineRepresentative_last ι g P hP
  have hlastQ := affineRepresentative_last ι g Q hQ
  have hdet : (affineRepresentative ι g P 1 - affineRepresentative ι g Q 1) *
      g (vectorMap ι T.rep) 0 +
      (affineRepresentative ι g Q 0 - affineRepresentative ι g P 0) * g (vectorMap ι T.rep) 1 = 0 := by
    simp [dot, cross, Fin.sum_univ_three, hT, hlastP, hlastQ] at hcol'
    exact hcol'
  have hdelta : affineRepresentative ι g Q 0 - affineRepresentative ι g P 0 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hdiff)
  have hfirst : g (vectorMap ι T.rep) 0 ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_add] at hdet
    have hone := (mul_eq_zero.mp hdet).resolve_left hdelta
    have hraw : g (vectorMap ι T.rep) = 0 := by
      funext j
      fin_cases j
      · exact hz
      · exact hone
      · exact hT
    apply T.rep_nonzero
    apply vectorMap_injective ι
    apply g.injective
    exact hraw.trans (by rw [map_zero, map_zero])
  refine ⟨hfirst, ?_⟩
  unfold directionSlope
  field_simp [hfirst, hdelta]
  linear_combination hdet

theorem directionSlope_injective (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (C : Finset (PlanePoint R))
    (hzero : ∀ T ∈ C, g (vectorMap ι T.rep) 2 = 0)
    (hfirst : ∀ T ∈ C, g (vectorMap ι T.rep) 0 ≠ 0) :
    Function.Injective (fun T : C => directionSlope ι g T.val) := by
  intro P Q heq
  by_contra hneq
  have hp := hfirst P.val P.property
  have hq := hfirst Q.val Q.property
  have hc : g (vectorMap ι P.val.rep) 1 * g (vectorMap ι Q.val.rep) 0 =
      g (vectorMap ι Q.val.rep) 1 * g (vectorMap ι P.val.rep) 0 :=
    (div_eq_div_iff hp hq).mp heq
  have hv : g (vectorMap ι Q.val.rep) =
      (g (vectorMap ι Q.val.rep) 0 / g (vectorMap ι P.val.rep) 0) • g (vectorMap ι P.val.rep) := by
    funext j
    fin_cases j
    · exact (div_mul_cancel₀ _ hp).symm
    · change g (vectorMap ι Q.val.rep) 1 =
        (g (vectorMap ι Q.val.rep) 0 / g (vectorMap ι P.val.rep) 0) * g (vectorMap ι P.val.rep) 1
      field_simp [hp]
      linear_combination -hc
    · change g (vectorMap ι Q.val.rep) 2 =
        (g (vectorMap ι Q.val.rep) 0 / g (vectorMap ι P.val.rep) 0) * g (vectorMap ι P.val.rep) 2
      rw [hzero P.val P.property, hzero Q.val Q.property, mul_zero]
  apply RationalPlanePointModel.representatives_distinct ι C P Q hneq
    (g (vectorMap ι Q.val.rep) 0 / g (vectorMap ι P.val.rep) 0)
  apply g.injective
  rw [map_smul]
  exact hv

theorem hyperbola_slope (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (b⁻¹ - a⁻¹) / (b - a) = -(a * b)⁻¹ := by
  field_simp [ha, hb, sub_ne_zero.mpr (Ne.symm hab)]
  ring

theorem parabola_slope (a b : K) (hab : a ≠ b) :
    (b ^ 2 - a ^ 2) / (b - a) = a + b := by
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

end Cylinder.ConicAffineDirections
end
