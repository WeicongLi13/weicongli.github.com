module

public import Cylinder.GlobalMomentCofactors
public import Cylinder.GlobalMomentArithmetic

/-! The linear and quadratic component forms agree, by their true
cleared relation supports and the actual excess bound. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentAgreement

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition Cylinder.PlaneCurveFactors
open Cylinder.MinimumEquationComponentSets Cylinder.DirectionCurveComponentCounting
open Cylinder.DirectionComponentDecomposition Cylinder.GlobalMomentSupport Cylinder.GlobalMomentCofactors

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 1000000 in
theorem component_forms_agree {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F G Q : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (hG : G ∈ factors F) (hQ : Q ∈ factors F) (hGQ : G ≠ Q)
    (u m : directionSet p S b hb → CurveField p) (hu : ∀ P, u P ≠ 0)
    (hurel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3))
    (a : ℕ) (ha : a ≤ 2)
    (hmrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) m (p - 3 - a))
    (qi qj : MvPolynomial (Fin 3) (CurveField p)) (hqi : qi.IsHomogeneous a) (hqj : qj.IsHomogeneous a)
    (hidentityi : ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G →
        m P = eval (representatives (embedding p) (directionSet p S b hb) P) qi * u P)
    (hidentityj : ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F Q →
        m P = eval (representatives (embedding p) (directionSet p S b hb) P) qj * u P) : qi = qj := by
  by_contra hne
  let D := directionSet p S b hb
  let e := G.totalDegree
  let t := Q.totalDegree
  let w := clearedDifference (embedding p) D F G Q m u qj
  let j := s - e - t
  let d := p - 3 - a - j
  have hnum := DirectionCurveProposition.direction_curve p hp hcard hS hnon hb s hs
  have hsupper := hnum.2.1
  have hdegree := pair_factor_degree_remainder F G Q s hF hF0 hsq hG hQ hGQ
  change j + e + t = s at hdegree
  obtain ⟨HG, hGHG⟩ := factor_dvd F G hG
  obtain ⟨HQ, hQHQ⟩ := factor_dvd F Q hQ
  have hdataG := hcomp G hG HG hGHG
  have hdataQ := hcomp Q hQ HQ hQHQ
  have hedelta := hdataG.2.2.2.2.2.2
  have htdelta := hdataQ.2.2.2.2.2.2
  have hGcard := hdataG.2.2.2.2.1
  rw [hdataG.1] at hGcard
  change e * (p - s) ≤ (componentPoints D F G).card at hGcard
  have hGhom : G.IsHomogeneous e := factor_homogeneous F s hF hF0 G hG
  have hGirr : Irreducible (MvPolynomial.map (embedding p) G) :=
    MinimumEquationAbsoluteFactors.factors_absolutely_irreducible p D s
      ((RationalMinimumEquation.initialDegree_iff (embedding p) D s).mp hs) F hF hF0 hzero G hG
  have he : 4 ≤ e := by change p - 2 * s + 1 ≤ e at hedelta; omega
  have ht : 4 ≤ t := by change p - 2 * s + 1 ≤ t at htdelta; omega
  have hae : a < e := by omega
  have hat : a ≤ t := by omega
  have had : a ≤ p - 3 := by omega
  have hjd : s - G.totalDegree - Q.totalDegree ≤ p - 3 - a := by omega
  have hwrel : PowerEvaluationRelation.Relation (representatives (embedding p) D) w d :=
    clearedDifference_relation (embedding p) D F G Q s (p - 3) a hF hF0 hsq hG hQ hGQ
      m u qj hqj had hjd hurel hmrel
  have hsupp := clearedDifference_support_on_first_factor (embedding p) D F G Q
    hF0 hG hQ hGQ hzero m u qj hidentityj
  have hlower := clearedDifference_support_card_lower (embedding p) D F G Q e a
    hGhom hGirr m u hu qi qj hqi hqj hne hae hidentityi
  change (componentPoints D F G).card ≤ (supportIndices w).card + e * a at hlower
  have hrem : p - s - a + a = p - s := by omega
  have hlowcard : e * (p - s - a) ≤ (supportIndices w).card := by
    nlinarith only [hGcard, hlower, hrem]
  have hstrict : e * (e - 1) < (supportIndices w).card := by
    have hstrictmul := Nat.mul_lt_mul_of_pos_left
      (show e - 1 < p - s - a by omega) (show 0 < e by omega)
    exact hstrictmul.trans_le hlowcard
  have hchar := support_character_lower (representatives (embedding p) D)
    (representatives_nonzero _ _) (representatives_distinct _ _)
    (MvPolynomial.map (embedding p) G) e (hGhom.map _) hGirr w d hwrel
    (fun P hP => (hsupp P hP).1) hstrict
  have hds : d + 3 - e = (p - s) + (t - a) := by dsimp [d]; omega
  rw [hds] at hchar
  have hupper := clearedDifference_support_card_upper (embedding p) D F G Q
    hF0 hG hQ hGQ hzero m u qj hidentityj
  change (supportIndices w).card ≤ (componentPoints D F G).card + (intersectionPoints D F).card at hupper
  have hex := componentExcess_identity p hb s F G hG hcomp
  change e * (p - s) + componentExcess p hb s F G = (componentPoints D F G).card at hex
  have hlam := component_excess_add_intersections_le_total p hb s F G hF hF0 hsq hG hcomp
  have hloweps : e * (t - a) ≤ totalExcess p hb s := by
    nlinarith only [hchar, hupper, hex, hlam]
  have higheps := total_excess_upper p hp hcard hS hnon hb s hs
  have highepsZ : (4 : ℤ) * totalExcess p hb s + p ≤ ((p - 2 * s : ℕ) : ℤ) ^ 2 + 2 := by
    exact_mod_cast higheps
  have hlowepsZ : (e : ℤ) * ((t : ℤ) - a) ≤ totalExcess p hb s := by
    have h : ((e * (t - a) : ℕ) : ℤ) ≤ totalExcess p hb s := by exact_mod_cast hloweps
    simpa only [Nat.cast_mul, Nat.cast_sub hat] using h
  exact GlobalMomentArithmetic.component_agreement_obstruction (p : ℤ)
    ((p - 2 * s : ℕ) : ℤ) (e : ℤ) (t : ℤ) (a : ℤ) (totalExcess p hb s : ℤ)
    (by exact_mod_cast hp) (by exact_mod_cast (show 3 ≤ p - 2 * s by omega))
    (by exact_mod_cast hedelta) (by exact_mod_cast htdelta) (by exact_mod_cast ha) hlowepsZ
    (by nlinarith)

end Cylinder.GlobalMomentAgreement

end
