module

public import Cylinder.LocalCommonDenominator
public import Cylinder.WeightedFormRelations

/-! Genuine common residual numerator data and actual curve point
recurrences imply the desired linear and quadratic interpolation on the
whole point set, including zeros of the common denominator. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalWeightedInterpolation

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.LocalCurveInterpolation Cylinder.LocalCommonDenominator
open Cylinder.WeightedFormRelations
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem multiply_relation (v : I → Fin 3 → K) (u : I → K) (d q : ℕ)
    (hq : q ≤ d) (Q : PlaneRing K) (hQ : Q.IsHomogeneous q)
    (hrel : PowerEvaluationRelation.Relation v u d) :
    PowerEvaluationRelation.Relation v (fun i => eval (v i) Q * u i) (d - q) := by
  intro P hP
  have hhom : (Q * P).IsHomogeneous d := by
    have hh := hQ.mul hP
    rwa [Nat.add_sub_cancel' hq] at hh
  have hh := hrel (Q * P) hhom
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem interpolate_of_factor_and_cross (F A Q : PlaneRing K) (e m d q : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hA : A.IsHomogeneous m) (hA0 : A ≠ 0) (hm : 0 < m) (hme : m < e)
    (hQ : Q.IsHomogeneous q) (hqd : q ≤ d) (hd : e + m - 2 ≤ d - q)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (u μ : I → K)
    (hu : PowerEvaluationRelation.Relation v u d)
    (hμ : PowerEvaluationRelation.Relation v μ (d - q))
    (hcross : ∀ i, eval (v i) A * μ i = eval (v i) (A * Q) * u i) :
    ∀ i, μ i = eval (v i) Q * u i := by
  let c := fun i => μ i - eval (v i) Q * u i
  have hrel : PowerEvaluationRelation.Relation v c (d - q) := by
    intro P hP
    have hprod := multiply_relation v u d q hqd Q hQ hu P hP
    simp only [c, sub_mul, Finset.sum_sub_distrib, hμ P hP, hprod, sub_self]
  have hsupport : ∀ i, eval (v i) A ≠ 0 → c i = 0 := by
    intro i hi
    have hx := hcross i
    rw [map_mul] at hx
    apply (mul_eq_zero.mp (show eval (v i) A * c i = 0 by dsimp [c]; linear_combination hx)).resolve_left hi
  have hz := relation_zero_of_supported_on_lower_curve F A e m hF hirr hA hA0 hm hme
    v hv hsep hFzero c (d - q) hd hrel hsupport
  intro i
  exact sub_eq_zero.mp (congrFun hz i)

/-- The common numerator at index zero is the actual denominator. This
is derived from the actual initial degree and full support, not assumed. -/
theorem numerator_zero_eq_denominator (A : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hA : A.IsHomogeneous m) (hnum : (num 0).IsHomogeneous m) (hme : m < e)
    (v : I → Fin 3 → K) (hs : InitialDegree v e) (u : I → K) (hu : ∀ i, u i ≠ 0)
    (hcross : ∀ i, eval (v i) A * u i = eval (v i) (num 0) * u i) : num 0 = A := by
  have hinj := evaluationMap_injective_of_lt_initial v e m hs hme
  have hmap : evaluationMap v m ⟨num 0, hnum⟩ = evaluationMap v m ⟨A, hA⟩ := by
    funext i
    exact (mul_right_cancel₀ (hu i) (hcross i)).symm
  exact congrArg Subtype.val (hinj hmap)

/-- The entire final interpolation conclusion of `thm:local` follows
from genuine common residual numerator data. The remaining front half
of that theorem must construct these data from the numerical plateau. -/
theorem interpolate_of_common_numerators (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m d : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA0 : A ≠ 0) (hA : A.IsHomogeneous m)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hnum : ∀ n ≤ 2 * m + 2, (num n).IsHomogeneous (m + n))
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hs : InitialDegree v e) (hFzero : ∀ i, eval (v i) F = 0)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (μ : ℕ → I → K) (hμ0 : μ 0 = u)
    (hrel : ∀ n ≤ 2 * m + 2, PowerEvaluationRelation.Relation v (μ n) (d - n))
    (hcross : ∀ n ≤ 2 * m + 2, ∀ i, eval (v i) A * μ n i = eval (v i) (num n) * u i)
    (T : Finset I) (hcard : e * (5 * m + 2) < T.card)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      μ (n + 2) i / u i = (μ 1 i / u i) * (μ (n + 1) i / u i) -
        ((μ 1 i / u i) ^ 2 - μ 2 i / u i) * (μ n i / u i)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, μ 1 i = eval (v i) f * u i) ∧ (∀ i, μ 2 i = eval (v i) g * u i) := by
  have hnum0 : num 0 = A := numerator_zero_eq_denominator A num e m hA
    (by simpa only [Nat.add_zero] using hnum 0 (by omega)) (by omega) v hs u hu
    (by simpa only [hμ0] using hcross 0 (by omega))
  have hpoint : ∀ i ∈ T, ∀ n ≤ 2 * m + 2,
      eval (v i) (num n) = eval (v i) A * (μ n i / u i) := by
    intro i hi n hn
    rw [← mul_div_assoc]
    exact (eq_div_iff (hu i)).mpr (hcross n hn i).symm
  obtain ⟨f, g, hf, hg, hfirst, hsecond⟩ := forms_of_point_numerators F A num e m
    hF hirr hA0 hA hnum0 hnum hsmall v hv hsep hFzero T (fun i n => μ n i / u i) hpoint hrec hcard
  have hurel : PowerEvaluationRelation.Relation v u d := by
    simpa only [Nat.sub_zero, hμ0] using hrel 0 (by omega)
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · apply interpolate_of_factor_and_cross F A f e m d 1 hF hirr hA hA0 hm (by omega) hf (by omega)
      (by omega) v hv hsep hFzero u (μ 1) hurel (hrel 1 (by omega))
    simpa only [hfirst] using hcross 1 (by omega)
  · apply interpolate_of_factor_and_cross F A g e m d 2 hF hirr hA hA0 hm (by omega) hg (by omega)
      (by omega) v hv hsep hFzero u (μ 2) hurel (hrel 2 (by omega))
    simpa only [hsecond] using hcross 2 (by omega)

#print axioms interpolate_of_factor_and_cross
#print axioms numerator_zero_eq_denominator
#print axioms interpolate_of_common_numerators

end Cylinder.LocalWeightedInterpolation

end
