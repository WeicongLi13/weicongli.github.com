module

public import Cylinder.LocalFactorCancellation
public import Cylinder.LocalCharacterData

/-! The saturated residual plateau constructs the common numerators;
support interpolation cancels their common factor globally; the actual
point recurrences then give the complete linear/quadratic conclusion. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalResidualInterpolation

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.SaturatedPlaneLine Cylinder.NumericCharacterSequence
open Cylinder.LocalResidualNumerators Cylinder.LocalFactorCancellation
open Cylinder.LocalWeightedInterpolation
open scoped Classical

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

/-- The residual-ideal stage of `thm:local`, using true saturated ideals
and true residual representative data. The common numerator factor and
the desired linear/quadratic forms are all constructed by this theorem. -/
theorem interpolate_of_residual_plateau (F : PlaneRing K) (J : Ideal (PlaneRing K))
    (e β m d : ℕ) (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hJ : Saturated J) (hm : 0 < m) (hmβ : m ≤ β)
    (hsmall : 4 * m + 2 < e) (hβ : β + 2 * m + 2 ≤ e - 2) (hd : 2 * e ≤ d)
    (Q : ℕ → PlaneRing K) (hQhom : ∀ q ≤ 2 * m + 2, (Q q).IsHomogeneous (β + q))
    (hQJ : ∀ q ≤ 2 * m + 2, Q q ∈ J) (hQ0 : Q 0 ≠ 0)
    (h0 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (β + 2 * m + 1) = β - m)
    (h1 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (β + 2 * m + 2) = β - m)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hs : InitialDegree v e) (hFzero : ∀ i, eval (v i) F = 0)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (μ : ℕ → I → K) (hμ0 : μ 0 = u)
    (hrel : ∀ q ≤ 2 * m + 2, PowerEvaluationRelation.Relation v (μ q) (d - q))
    (hcross : ∀ q ≤ 2 * m + 2, ∀ i, eval (v i) (Q 0) * μ q i = eval (v i) (Q q) * u i)
    (T : Finset I) (hcard : e * (5 * m + 2) < T.card)
    (hrec : ∀ i ∈ T, ∀ q, q + 2 ≤ 2 * m + 2 →
      μ (q + 2) i / u i = (μ 1 i / u i) * (μ (q + 1) i / u i) -
        ((μ 1 i / u i) ^ 2 - μ 2 i / u i) * (μ q i / u i)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, μ 1 i = eval (v i) f * u i) ∧ (∀ i, μ 2 i = eval (v i) g * u i) := by
  obtain ⟨K₀, A, num, hK0, hK, hA0, hA, hQKA, hnum0, hnum⟩ :=
    common_numerators J hJ β m hmβ Q hQhom hQJ hQ0 h0 h1
  have hurel : PowerEvaluationRelation.Relation v u d := by
    simpa only [Nat.sub_zero, hμ0] using hrel 0 (by omega)
  have hcross' := common_cross_relations F K₀ A num Q e β m d hF hirr hK hK0 hmβ hA
    (fun q hq => (hnum q hq).1) hQKA (fun q hq => (hnum q hq).2) hβ hd v hv hsep hFzero u μ hurel hrel hcross
  exact interpolate_of_common_numerators F A num e m d hF hirr hA0 hA hm hsmall hd
    (fun q hq => (hnum q hq).1) v hv hsep hs hFzero u hu μ hμ0 hrel hcross' T hcard hrec

#print axioms interpolate_of_residual_plateau

end Cylinder.LocalResidualInterpolation

end
