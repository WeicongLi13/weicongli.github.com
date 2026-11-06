module

public import Cylinder.GlobalMomentAgreement
public import Cylinder.GlobalMomentIntersection

/-! The global moment conclusion, once the preceding component
interpolation proposition has supplied the actual component forms. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentsFromComponents

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition Cylinder.PlaneCurveFactors
open Cylinder.MinimumEquationComponentSets Cylinder.GlobalMomentSupport

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 800000 in
theorem global_component_form {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (u m : directionSet p S b hb → CurveField p) (hu : ∀ P, u P ≠ 0)
    (hurel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3))
    (a : ℕ) (ha : a ≤ 2)
    (hmrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) m (p - 3 - a))
    (q : factors F → MvPolynomial (Fin 3) (CurveField p))
    (hq : ∀ G, (q G).IsHomogeneous a)
    (hidentity : ∀ G : factors F, ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G.val →
        m P = eval (representatives (embedding p) (directionSet p S b hb) P) (q G) * u P) :
    ∃ q₀ : MvPolynomial (Fin 3) (CurveField p), q₀.IsHomogeneous a ∧
      (∀ G, q G = q₀) ∧ ∀ P : directionSet p S b hb,
        m P = eval (representatives (embedding p) (directionSet p S b hb) P) q₀ * u P := by
  let D := directionSet p S b hb
  letI : Nonempty D := DirectionCurveBounds.direction_nonempty p hcard hS hnon hb
  let P : D := Classical.choice inferInstance
  obtain ⟨G, hG, _hGzero⟩ := (eval_zero_iff_factor_zero F hF0 P.val.rep).mp (hzero P.val P.property)
  let G₀ : factors F := ⟨G, hG⟩
  have hcommon : ∀ Q : factors F, q Q = q G₀ := by
    intro Q
    by_cases hQG : Q = G₀
    · rw [hQG]
    · exact GlobalMomentAgreement.component_forms_agree p hp hcard hS hnon hb s hs
        F Q.val G₀.val hF hF0 hsq hzero hcomp Q.property G₀.property
        (fun h => hQG (Subtype.ext h)) u m hu hurel a ha hmrel (q Q) (q G₀)
        (hq Q) (hq G₀) (hidentity Q) (hidentity G₀)
  have hdegrees := DirectionCurveProposition.direction_curve p hp hcard hS hnon hb s hs
  have hsupper := hdegrees.2.1
  have hweighted := relation_after_polynomial_multiplication (representatives (embedding p) D)
    u (p - 3) a (by omega) (q G₀) (hq G₀) hurel
  have hweighted' : PowerEvaluationRelation.Relation (representatives (embedding p) D)
      (fun i => eval (representatives (embedding p) D i) (q G₀) * u i) (p - 3 - a) := by
    simpa only [mul_comm] using hweighted
  have hdiff := relation_sub (representatives (embedding p) D) m _ (p - 3 - a) hmrel hweighted'
  have hzeroall := GlobalMomentIntersection.actual_intersection_relation_zero p D s hs F hF hF0
    hsq hzero (fun i => m i - eval (representatives (embedding p) D i) (q G₀) * u i)
    (p - 3 - a) (by omega) hdiff (by
      intro Q hQ i hi
      have hid := hidentity ⟨Q, hQ⟩ i hi
      rw [hcommon ⟨Q, hQ⟩] at hid
      rw [hid, sub_self])
  refine ⟨q G₀, hq G₀, hcommon, ?_⟩
  intro i
  exact sub_eq_zero.mp (congrFun hzeroall i)

set_option maxHeartbeats 800000 in
theorem global_moment_forms_from_components {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (u m₂ m₃ : directionSet p S b hb → CurveField p) (hu : ∀ P, u P ≠ 0)
    (hurel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3))
    (hm₂ : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) m₂ (p - 4))
    (hm₃ : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) m₃ (p - 5))
    (fi gi : factors F → MvPolynomial (Fin 3) (CurveField p))
    (hfi : ∀ G, (fi G).IsHomogeneous 1) (hgi : ∀ G, (gi G).IsHomogeneous 2)
    (hidf : ∀ G : factors F, ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G.val →
        m₂ P = eval (representatives (embedding p) (directionSet p S b hb) P) (fi G) * u P)
    (hidg : ∀ G : factors F, ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G.val →
        m₃ P = eval (representatives (embedding p) (directionSet p S b hb) P) (gi G) * u P) :
    ∃ f g : MvPolynomial (Fin 3) (CurveField p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ G, fi G = f) ∧ (∀ G, gi G = g) ∧
      (∀ P : directionSet p S b hb,
        m₂ P = eval (representatives (embedding p) (directionSet p S b hb) P) f * u P) ∧
      ∀ P : directionSet p S b hb,
        m₃ P = eval (representatives (embedding p) (directionSet p S b hb) P) g * u P := by
  obtain ⟨f, hf, hfc, hfv⟩ := global_component_form p hp hcard hS hnon hb s hs F hF hF0 hsq
    hzero hcomp u m₂ hu hurel 1 (by decide)
    (by simpa only [Nat.sub_sub, Nat.reduceAdd] using hm₂) fi hfi hidf
  obtain ⟨g, hg, hgc, hgv⟩ := global_component_form p hp hcard hS hnon hb s hs F hF hF0 hsq
    hzero hcomp u m₃ hu hurel 2 (by decide)
    (by simpa only [Nat.sub_sub, Nat.reduceAdd] using hm₃) gi hgi hidg
  exact ⟨f, g, hf, hg, hfc, hgc, hfv, hgv⟩

end Cylinder.GlobalMomentsFromComponents

end
