module

public import Cylinder.LocalResidualFamily
public import Cylinder.LocalResidualHilbert
public import Cylinder.LocalResidualInterpolation
public import Cylinder.LocalRepresentativeTransport
public import Cylinder.LocalCoprimeEquation

/-! Local interpolation from the manuscript's actual finite point geometry,
connected numerical character, weighted relations and point recurrence. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalCurveTheorem
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.ProjectiveChartData Cylinder.LocalResidualRepresentatives
open Cylinder.LocalResidualFamily Cylinder.LocalResidualHilbert Cylinder.LocalCharacterData
open Cylinder.LocalResidualInterpolation Cylinder.LocalRepresentativeTransport
open Cylinder.ComponentCharacterNumeric Cylinder.HilbertCharacterFormulas

variable {K : Type*} [Field K] [Infinite K]

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
    (T : Finset D) (hcard : e * (5 * m + 2) < T.card)
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

/-- The complete local interpolation theorem on the original projective point
set. Every residual representative, common factor and numerator is constructed
from the stated numerical character and weighted point relations. -/
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
    (T : Finset D) (hcard : e * (5 * m + 2) < T.card)
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

#print axioms interpolate_in_good_chart
#print axioms local_curve_interpolation

end Cylinder.LocalCurveTheorem
end
