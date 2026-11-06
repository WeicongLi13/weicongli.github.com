module

public import Cylinder.LocalCurveTheorem

/-! The current manuscript's local moment plateau lemma, with the sharp
point threshold e * (4 * m + 2).  The first cleared recurrence is needed
only through n = m; after removing the linear pole, the second cleared
recurrence has degree at most 4 * m + 2 through n = 2 * m. Both vanish on
all recurrence points, including zeros of the common denominator. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.FinalLocalCurveTheorem

open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.LocalCurveInterpolation Cylinder.LocalRecurrenceClearing
open Cylinder.LocalCommonDenominator Cylinder.LocalWeightedInterpolation
open Cylinder.SaturatedPlaneLine Cylinder.NumericCharacterSequence
open Cylinder.LocalResidualNumerators Cylinder.LocalFactorCancellation
open Cylinder.ProjectiveChartData Cylinder.LocalResidualRepresentatives
open Cylinder.LocalResidualFamily Cylinder.LocalResidualHilbert Cylinder.LocalCharacterData
open Cylinder.LocalRepresentativeTransport Cylinder.ComponentCharacterNumeric
open Cylinder.HilbertCharacterFormulas

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]
theorem firstCleared_eq_zero (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA : A.IsHomogeneous m)
    (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i))
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (4 * m + 2) < T.card) (n : ℕ) (hn : n ≤ m) : firstCleared A num n = 0 := by
  apply polynomial_eq_zero_of_many_points F _ e (3 * m + n + 2) hF hirr
    (firstCleared_homogeneous A num m (2 * m + 2) n hA hnum (by omega)) (by omega)
    (fun i : T => v i.val) (fun i => hv i.val)
    (by intro i j hij c; exact hsep i.val j.val (fun heq => hij (Subtype.ext heq)) c)
  · intro i
    exact ⟨hFzero i.val, firstCleared_eval_zero A num (v i.val) (h i.val) (2 * m + 2) n
      (by omega) (hcommon i.val i.property) (hrec i.val i.property n (by omega))⟩
  · have hbound : e * (3 * m + n + 2) ≤ e * (4 * m + 2) := Nat.mul_le_mul_left e (by omega)
    simpa only [Fintype.card_coe] using lt_of_le_of_lt hbound hcard

theorem secondCleared_eq_zero (F A f : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA : A.IsHomogeneous m) (hf : f.IsHomogeneous 1)
    (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i)) (hfirst : num 1 = A * f)
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (4 * m + 2) < T.card) (n : ℕ) (hn : n ≤ 2 * m) : secondCleared A f num n = 0 := by
  apply polynomial_eq_zero_of_many_points F _ e (2 * m + n + 2) hF hirr
    (secondCleared_homogeneous A f num m (2 * m + 2) n hA hf hnum (by omega)) (by omega)
    (fun i : T => v i.val) (fun i => hv i.val)
    (by intro i j hij c; exact hsep i.val j.val (fun heq => hij (Subtype.ext heq)) c)
  · intro i
    exact ⟨hFzero i.val, secondCleared_eval_zero A f num (v i.val) (h i.val) (2 * m + 2) n
      (by omega) hfirst (hcommon i.val i.property) (hrec i.val i.property n (by omega))⟩
  · have hbound : e * (2 * m + n + 2) ≤ e * (4 * m + 2) := Nat.mul_le_mul_left e (by omega)
    simpa only [Fintype.card_coe] using lt_of_le_of_lt hbound hcard

theorem forms_of_point_numerators (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA0 : A ≠ 0) (hA : A.IsHomogeneous m)
    (hnum0 : num 0 = A) (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i))
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (4 * m + 2) < T.card) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧ num 1 = A * f ∧ num 2 = A * g := by
  obtain ⟨f, hf, hfirst⟩ := first_quotient_linear A num m hA0 hA hnum0 (hnum 1 (by omega))
    (firstCleared_eq_zero F A num e m hF hirr hA hnum hsmall v hv hsep hFzero T h hcommon hrec hcard)
  obtain ⟨g, hg, hsecond⟩ := second_quotient_quadratic A f num m hA0 hA hf hnum0 hfirst
    (hnum 2 (by omega))
    (secondCleared_eq_zero F A f num e m hF hirr hA hf hnum hfirst hsmall v hv hsep hFzero T h hcommon hrec hcard)
  exact ⟨f, g, hf, hg, hfirst, hsecond⟩

theorem interpolate_of_common_numerators (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m d : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA0 : A ≠ 0) (hA : A.IsHomogeneous m)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hnum : ∀ n ≤ 2 * m + 2, (num n).IsHomogeneous (m + n))
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hs : InitialDegree v e) (hFzero : ∀ i, eval (v i) F = 0)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (μ : ℕ → I → K) (hμ0 : μ 0 = u)
    (hrel : ∀ n ≤ 2 * m + 2, PowerEvaluationRelation.Relation v (μ n) (d - n))
    (hcross : ∀ n ≤ 2 * m + 2, ∀ i, eval (v i) A * μ n i = eval (v i) (num n) * u i)
    (T : Finset I) (hcard : e * (4 * m + 2) < T.card)
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
    (T : Finset I) (hcard : e * (4 * m + 2) < T.card)
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

theorem interpolate_in_good_chart (c : Chart K) (F G : PlaneRing K) (e t d β m : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t)
    (D : Finset (PlanePointModel.Plane K)) [Nonempty D]
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (hdegree : (e : ℤ) + t - 3 - d = β) (het : e ≤ t)
    (hm : 0 < m) (hmβ : m ≤ β) (hsmall : 4 * m + 2 < e)
    (hβ : β + 2 * m + 2 ≤ e - 2) (hd : 2 * e ≤ d)
    (hv : ∀ P : D, c.normalizedPoint P.val ≠ 0)
    (hsep : ProjectivelyDistinct (fun P : D => c.normalizedPoint P.val))
    (hs : InitialDegree (fun P : D => c.normalizedPoint P.val) e)
    (u : D → K) (hu : ∀ P, u P ≠ 0) (μ : ℕ → D → K) (hμ0 : μ 0 = u)
    (hrel : ∀ q ≤ 2 * m + 2,
      PowerEvaluationRelation.Relation (fun P : D => c.normalizedPoint P.val) (μ q) (d - q))
    (hconn : ∀ i, 0 < i → i < e →
      numericalCharacter (fun P : D => c.normalizedPoint P.val) (i - 1) ≤
        numericalCharacter (fun P : D => c.normalizedPoint P.val) i + 1)
    (hplateau : ∀ r < 4,
      increment (numericalCharacter (fun P : D => c.normalizedPoint P.val)) d (3 * m + r) = m)
    (T : Finset D) (hcard : e * (4 * m + 2) < T.card)
    (hrec : ∀ P ∈ T, ∀ q, q + 2 ≤ 2 * m + 2 →
      μ (q + 2) P / u P = (μ 1 P / u P) * (μ (q + 1) P / u P) -
        ((μ 1 P / u P) ^ 2 - μ 2 P / u P) * (μ q P / u P)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P : D, μ 1 P = eval (c.normalizedPoint P.val) f * u P) ∧
      (∀ P : D, μ 2 P = eval (c.normalizedPoint P.val) g * u P) := by
  have hurel : PowerEvaluationRelation.Relation (fun P : D => c.normalizedPoint P.val) u d := by
    simpa only [Nat.sub_zero, hμ0] using hrel 0 (by omega)
  obtain ⟨Q, hQhom, hQJ, hQ0, hcross⟩ := exists_residual_family c F G e t d β (2 * m + 2)
    he ht hF hG hgood D hpoints hdegree (by omega) u hu μ hμ0 hrel
  obtain ⟨h₀, h₁⟩ := actual_residual_first_differences c F G e t d β m he ht hF hG hgood D
    hpoints hdegree het hm hmβ hsmall hβ hd hv hsep hs u hu hurel hconn hplateau
  have hFzero : ∀ P : D, eval (c.normalizedPoint P.val) F = 0 := by
    intro P
    change eval ((c.line P.val.rep)⁻¹ • P.val.rep) F = 0
    rw [LinearEvaluationTransport.homogeneous_eval_smul F e hF, (hpoints P).1, mul_zero]
  exact interpolate_of_residual_plateau F (ResidualIdeal F G D) e β m d hF hirr
    (actual_residual_saturated c F G e t hF hG hgood D) hm hmβ hsmall hβ hd
    Q hQhom hQJ hQ0 h₀ h₁ (fun P : D => c.normalizedPoint P.val) hv hsep hs hFzero
    u hu μ hμ0 hrel hcross T hcard hrec

theorem local_curve_interpolation (D : Finset (PlanePointModel.Plane K))
    (F : PlaneRing K) (e d m : ℕ) (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hs : InitialDegree (PlanePointModel.representatives D) e)
    (hFzero : ∀ P : D, eval P.val.rep F = 0) (hm : 0 < m)
    (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (u : D → K) (hu : ∀ P, u P ≠ 0) (μ : ℕ → D → K) (hμ0 : μ 0 = u)
    (hrel : ∀ q ≤ 2 * m + 2,
      PowerEvaluationRelation.Relation (PlanePointModel.representatives D) (μ q) (d - q))
    (hconn : ∀ i, 0 < i → i < e →
      numericalCharacter (PlanePointModel.representatives D) (i - 1) ≤
        numericalCharacter (PlanePointModel.representatives D) i + 1)
    (hplateau : ∀ r < 4,
      increment (numericalCharacter (PlanePointModel.representatives D)) d (3 * m + r) = m)
    (T : Finset D) (hcard : e * (4 * m + 2) < T.card)
    (hrec : ∀ P ∈ T, ∀ q, q + 2 ≤ 2 * m + 2 →
      μ (q + 2) P / u P = (μ 1 P / u P) * (μ (q + 1) P / u P) -
        ((μ 1 P / u P) ^ 2 - μ 2 P / u P) * (μ q P / u P)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P : D, μ 1 P = eval P.val.rep f * u P) ∧
      (∀ P : D, μ 2 P = eval P.val.rep g * u P) := by
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hcard)
  letI : Nonempty D := ⟨hT.choose⟩
  let v := PlanePointModel.representatives D
  have hv : ∀ P : D, v P ≠ 0 := PlanePointModel.representatives_nonzero D
  have hsep : ProjectivelyDistinct v := PlanePointModel.representatives_distinct D
  have hurel : PowerEvaluationRelation.Relation v u d := by
    simpa only [Nat.sub_zero, hμ0] using hrel 0 (by omega)
  let β := increment (numericalCharacter v) d (e - 1)
  let t := numericalCharacter v (e - 1)
  obtain ⟨hmβ, hβupper, htdegree, hβ⟩ := actual_beta_bounds v hv hsep e d m hs u hu hurel
    hm hsmall hd hconn (by simpa only [show 3 * m + 3 = 3 * m + (3 : ℕ) by omega] using hplateau 3 (by omega))
  obtain ⟨het, G, hG0, hG, hGzero, hcop⟩ := LocalCoprimeEquation.exists_coprime_equation
    v hv hsep e hs F hirr hF hFzero
  have he : 0 < e := by omega
  have ht : 0 < t := by dsimp only [t]; omega
  have hdegree : (e : ℤ) + t - 3 - d = β := by
    change t = d + 3 - e + β at htdegree
    omega
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hirr.ne_zero hG0 hcop
  have hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0 :=
    fun P => ⟨hFzero P, hGzero P⟩
  have hchart := point_line_ne_zero c F G e t hgood D hpoints
  let a : D → K := fun P => (c.line P.val.rep)⁻¹
  have ha : ∀ P, a P ≠ 0 := fun P => inv_ne_zero (hchart P)
  let v' := fun P : D => a P • v P
  have hv' : ∀ P : D, c.normalizedPoint P.val ≠ 0 := nonzero_rescaling v hv a ha
  have hsep' : ProjectivelyDistinct (fun P : D => c.normalizedPoint P.val) := distinct_rescaling v hsep a ha
  have hs' : InitialDegree (fun P : D => c.normalizedPoint P.val) e :=
    (initialDegree_rescaling v a ha e).mpr hs
  have hchar : numericalCharacter (fun P : D => c.normalizedPoint P.val) = numericalCharacter v :=
    numericalCharacter_rescaling v a ha
  let u' : D → K := fun P => u P / a P ^ d
  let μ' : ℕ → D → K := fun q P => μ q P / a P ^ (d - q)
  have hu' : ∀ P, u' P ≠ 0 := fun P => div_ne_zero (hu P) (pow_ne_zero d (ha P))
  have hμ0' : μ' 0 = u' := by
    funext P
    simp only [μ', u', Nat.sub_zero, hμ0]
  have hrel' : ∀ q ≤ 2 * m + 2,
      PowerEvaluationRelation.Relation (fun P : D => c.normalizedPoint P.val) (μ' q) (d - q) := by
    intro q hq
    exact LinearEvaluationTransport.relation_after_rescaling v (μ q) a ha (d - q) (hrel q hq)
  have hconn' : ∀ i, 0 < i → i < e →
      numericalCharacter (fun P : D => c.normalizedPoint P.val) (i - 1) ≤
        numericalCharacter (fun P : D => c.normalizedPoint P.val) i + 1 := by
    simpa only [hchar] using hconn
  have hplateau' : ∀ r < 4,
      increment (numericalCharacter (fun P : D => c.normalizedPoint P.val)) d (3 * m + r) = m := by
    simpa only [hchar] using hplateau
  have hrec' : ∀ P ∈ T, ∀ q, q + 2 ≤ 2 * m + 2 →
      μ' (q + 2) P / u' P = (μ' 1 P / u' P) * (μ' (q + 1) P / u' P) -
        ((μ' 1 P / u' P) ^ 2 - μ' 2 P / u' P) * (μ' q P / u' P) := by
    intro P hP q hq
    have hratio (n : ℕ) (hn : n ≤ 2 * m + 2) : μ' n P / u' P = a P ^ n * (μ n P / u P) :=
      quotient_rescaling (a P) (μ n P) (u P) (ha P) (hu P) d n (by omega)
    rw [hratio (q + 2) hq, hratio 1 (by omega), hratio (q + 1) (by omega),
      hratio 2 (by omega), hratio q (by omega), pow_one]
    exact recurrence_rescaling (a P) (fun n => μ n P / u P) q (hrec P hP q hq)
  obtain ⟨f, g, hf, hg, hfirst, hsecond⟩ := interpolate_in_good_chart c F G e t d β m
    he ht hF hirr hG hgood D hpoints hdegree het hm hmβ hsmall hβ hd
    hv' hsep' hs' u' hu' μ' hμ0' hrel' hconn' hplateau' T hcard hrec'
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · intro P
    exact interpolation_unscaling (a P) (μ 1 P) (u P) (ha P) d 1 (by omega) P.val.rep f hf (hfirst P)
  · intro P
    exact interpolation_unscaling (a P) (μ 2 P) (u P) (ha P) d 2 (by omega) P.val.rep g hg (hsecond P)
#print axioms local_curve_interpolation

end Cylinder.FinalLocalCurveTheorem
end