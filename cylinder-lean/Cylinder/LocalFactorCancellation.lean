module

public import Cylinder.LocalResidualNumerators
public import Cylinder.LocalWeightedInterpolation

/-! Common residual factors cancel on all actual curve points, including
their zeros, by genuine complete-intersection relation interpolation. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalFactorCancellation

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LocalCurveInterpolation
open Cylinder.LocalWeightedInterpolation
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem constant_form_eval_ne_zero (P : PlaneRing K) (hP : P.IsHomogeneous 0)
    (hP0 : P ≠ 0) (x : Fin 3 → K) : eval x P ≠ 0 := by
  have hC := totalDegree_eq_zero_iff_eq_C.mp (hP.totalDegree hP0)
  intro hx
  rw [hC, eval_C] at hx
  apply hP0
  rw [hC, hx, map_zero]

theorem cancel_on_curve (F K₀ A N : PlaneRing K) (e c m d q : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hK : K₀.IsHomogeneous c) (hK0 : K₀ ≠ 0) (hce : c < e)
    (hA : A.IsHomogeneous m) (hN : N.IsHomogeneous (m + q))
    (hqd : m + q ≤ d) (hdegree : e + c - 2 ≤ d - q - m)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (u μ : I → K)
    (hu : PowerEvaluationRelation.Relation v u d)
    (hμ : PowerEvaluationRelation.Relation v μ (d - q))
    (hcross : ∀ i, eval (v i) (K₀ * A) * μ i = eval (v i) (K₀ * N) * u i) :
    ∀ i, eval (v i) A * μ i = eval (v i) N * u i := by
  let w := fun i => eval (v i) A * μ i - eval (v i) N * u i
  have hArel := multiply_relation v μ (d - q) m (by omega) A hA hμ
  have hNrel := multiply_relation v u d (m + q) hqd N hN hu
  have hwrel : PowerEvaluationRelation.Relation v w (d - q - m) := by
    intro P hP
    have heq : d - (m + q) = d - q - m := by omega
    rw [heq] at hNrel
    have ha := hArel P hP
    have hn := hNrel P hP
    simp only [w, sub_mul, Finset.sum_sub_distrib, ha, hn, sub_self]
  have hsupport : ∀ i, eval (v i) K₀ ≠ 0 → w i = 0 := by
    intro i hi
    have hx := hcross i
    simp only [map_mul] at hx
    apply (mul_eq_zero.mp (show eval (v i) K₀ * w i = 0 by dsimp [w]; linear_combination hx)).resolve_left hi
  have hw : w = 0 := by
    by_cases hc : 0 < c
    · exact relation_zero_of_supported_on_lower_curve F K₀ e c hF hirr hK hK0 hc hce
        v hv hsep hFzero w (d - q - m) hdegree hwrel hsupport
    · have hc0 : c = 0 := by omega
      funext i
      exact hsupport i (constant_form_eval_ne_zero K₀ (hc0 ▸ hK) hK0 (v i))
  intro i
  exact sub_eq_zero.mp (congrFun hw i)

/-- All common-factor residual cross identities cancel globally. The
only input cross relation still contains K₀; cancellation is proved. -/
theorem common_cross_relations (F K₀ A : PlaneRing K) (num Q : ℕ → PlaneRing K) (e β m d : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hK : K₀.IsHomogeneous (β - m)) (hK0 : K₀ ≠ 0) (hmβ : m ≤ β)
    (hA : A.IsHomogeneous m) (hnum : ∀ q ≤ 2 * m + 2, (num q).IsHomogeneous (m + q))
    (hQ0 : Q 0 = K₀ * A) (hQnum : ∀ q ≤ 2 * m + 2, Q q = K₀ * num q)
    (hβ : β + 2 * m + 2 ≤ e - 2) (hd : 2 * e ≤ d)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (u : I → K) (μ : ℕ → I → K)
    (hu : PowerEvaluationRelation.Relation v u d)
    (hrel : ∀ q ≤ 2 * m + 2, PowerEvaluationRelation.Relation v (μ q) (d - q))
    (hcross : ∀ q ≤ 2 * m + 2, ∀ i, eval (v i) (Q 0) * μ q i = eval (v i) (Q q) * u i) :
    ∀ q ≤ 2 * m + 2, ∀ i, eval (v i) A * μ q i = eval (v i) (num q) * u i := by
  intro q hq
  apply cancel_on_curve F K₀ A (num q) e (β - m) m d q hF hirr hK hK0 (by omega)
    hA (hnum q hq) (by omega) (by omega) v hv hsep hFzero u (μ q) hu (hrel q hq)
  simpa only [hQ0, hQnum q hq] using hcross q hq

#print axioms cancel_on_curve
#print axioms common_cross_relations

end Cylinder.LocalFactorCancellation

end
