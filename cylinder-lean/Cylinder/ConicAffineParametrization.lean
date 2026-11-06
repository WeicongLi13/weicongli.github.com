module

public import Cylinder.ConicLineNormalForm
public import Cylinder.BMMVectorSecants
public import Cylinder.RationalPlanePointModel

/-! Actual rational projective points in the conic coordinates. Their
affine normalization is injective, and the two standard equations give
the literal parameter vectors (u,u⁻¹,1) and (u,u²,1). -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicAffineParametrization
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.RationalPlaneLine
open Cylinder.ProjectiveFieldEmbedding Cylinder.LinearEvaluationTransport
open Cylinder.BMMArcGeometry Cylinder.BMMVectorSecants Cylinder.BMMTriangleFrame

variable {R K : Type*} [Field R] [Field K]

def affineRepresentative (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint R) : Fin 3 → K :=
  (g (vectorMap ι P.rep) 2)⁻¹ • g (vectorMap ι P.rep)

theorem affineRepresentative_last (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint R) (hP : g (vectorMap ι P.rep) 2 ≠ 0) : affineRepresentative ι g P 2 = 1 :=
  inv_mul_cancel₀ hP

theorem affineRepresentative_injective (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (D : Finset (PlanePoint R))
    (hoff : ∀ P ∈ D, g (vectorMap ι P.rep) 2 ≠ 0) :
    Function.Injective (fun P : D => affineRepresentative ι g P.val) := by
  intro P Q hpq
  by_contra hneq
  have hs := congrArg (fun v : Fin 3 → K => g (vectorMap ι Q.val.rep) 2 • v) hpq
  change g (vectorMap ι Q.val.rep) 2 •
      ((g (vectorMap ι P.val.rep) 2)⁻¹ • g (vectorMap ι P.val.rep)) =
    g (vectorMap ι Q.val.rep) 2 •
      ((g (vectorMap ι Q.val.rep) 2)⁻¹ • g (vectorMap ι Q.val.rep)) at hs
  simp only [smul_smul] at hs
  rw [mul_inv_cancel₀ (hoff Q.val Q.property), one_smul] at hs
  have hrep : RationalPlanePointModel.representatives ι D Q =
      (g (vectorMap ι Q.val.rep) 2 * (g (vectorMap ι P.val.rep) 2)⁻¹) •
        RationalPlanePointModel.representatives ι D P := by
    apply g.injective
    rw [map_smul]
    exact hs.symm
  exact RationalPlanePointModel.representatives_distinct ι D P Q hneq _ hrep

theorem hyperbola_vector (v : Fin 3 → K) (hz : v 2 = 1)
    (hv : eval v (X 0 * X 1 - X 2 ^ 2 : PlaneRing K) = 0) :
    v 0 ≠ 0 ∧ v = ![v 0, (v 0)⁻¹, 1] := by
  have hprod : v 0 * v 1 = 1 := by
    simpa only [map_sub, map_mul, map_pow, eval_X, hz, one_pow, sub_eq_zero] using hv
  have hx : v 0 ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hprod
    exact zero_ne_one hprod
  have hy : v 1 = (v 0)⁻¹ := by
    calc
      v 1 = (v 0)⁻¹ * (v 0 * v 1) := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
      _ = (v 0)⁻¹ := by rw [hprod, mul_one]
  refine ⟨hx, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hy
  · exact hz

theorem parabola_vector (v : Fin 3 → K) (hz : v 2 = 1)
    (hv : eval v (X 0 ^ 2 - X 1 * X 2 : PlaneRing K) = 0) : v = ![v 0, (v 0) ^ 2, 1] := by
  have hy : v 1 = v 0 ^ 2 := by
    have h : v 0 ^ 2 - v 1 = 0 := by
      simpa only [map_sub, map_mul, map_pow, eval_X, hz, mul_one] using hv
    exact (sub_eq_zero.mp h).symm
  funext i
  fin_cases i
  · rfl
  · exact hy
  · exact hz

theorem collinear_after_field_coordinates (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P Q T : PlanePoint R)
    (hPQ : P ≠ Q) (hcol : Collinear P Q T) :
    PlaneCrossProduct.dot (PlaneCrossProduct.cross (g (vectorMap ι P.rep)) (g (vectorMap ι Q.rep)))
      (g (vectorMap ι T.rep)) = 0 := by
  let x := pairFrame P Q hPQ T.rep
  have hx2 : x 2 = 0 := secant_coordinate_zero P Q T hPQ hcol
  have hT : T.rep = x 0 • P.rep + x 1 • Q.rep := by
    apply (pairFrame P Q hPQ).injective
    rw [map_add, map_smul, map_smul, pairFrame_left, pairFrame_right]
    funext j
    fin_cases j <;> simp [x, hx2, Pi.smul_apply, smul_eq_mul]
  have hmapped : vectorMap ι T.rep = ι (x 0) • vectorMap ι P.rep + ι (x 1) • vectorMap ι Q.rep := by
    rw [hT]
    funext j
    change ι (x 0 * P.rep j + x 1 * Q.rep j) = ι (x 0) * ι (P.rep j) + ι (x 1) * ι (Q.rep j)
    rw [map_add, map_mul, map_mul]
  rw [hmapped, map_add, map_smul, map_smul]
  simp [PlaneCrossProduct.dot, PlaneCrossProduct.cross, Fin.sum_univ_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Cylinder.ConicAffineParametrization
end
