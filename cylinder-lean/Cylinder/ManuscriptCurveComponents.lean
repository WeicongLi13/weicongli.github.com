module

public import Cylinder.DirectionCurveProposition
public import Cylinder.MinimumEquationComponents

/-!
The component estimates in the direction-curve proposition. The point
set of a component is the actual filter where its cofactor is nonzero.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ManuscriptCurveComponents

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneBinaryReduction Cylinder.RationalMinimumEquation
open Cylinder.MinimumEquationComponents Cylinder.DirectionCurveBounds

variable (p : ℕ) [Fact p.Prime]

open Cylinder.DirectionCurveComponentBounds

theorem component_bounds (hp : 11 ≤ p)
    (D : Finset (PlanePoint (ZMod p)))
    (hcap : LineCap D ((p - 1) / 2))
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) D) s)
    (u : D → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) D) u (p - 3))
    (hsup : s ≤ (p - 3) / 2)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (G : MvPolynomial (Fin 3) (ZMod p)) (hG : Irreducible G)
    (H : MvPolynomial (Fin 3) (ZMod p)) (hGH : F = G * H) :
    (exclusivePoints D H).Nonempty ∧
      InitialDegree (representatives (embedding p)
        (exclusivePoints D H)) G.totalDegree ∧
      (∃ c : exclusivePoints D H → CurveField p,
        (∀ i, c i ≠ 0) ∧ PowerEvaluationRelation.Relation
          (representatives (embedding p) (exclusivePoints D H))
          c (p - 3 - s + G.totalDegree)) ∧
      G.totalDegree * (p - s) ≤ (exclusivePoints D H).card ∧
      (exclusivePoints D H).card ≤
        G.totalDegree * (G.totalDegree + p - 1) / 2 ∧
      p - 2 * s + 1 ≤ G.totalDegree := by
  let E := exclusivePoints D H
  have hsbase := (RationalMinimumEquation.initialDegree_iff (embedding p) D s).mp hs
  obtain ⟨hH0, hGhom, hHhom, hdeg, hepos⟩ := cofactor_data D s F hF hF0 G hG H hGH
  have hE := exclusive_nonempty D s hsbase F hF hF0 G hG H hGH
  obtain ⟨P, hP⟩ := hE
  let : Nonempty E := ⟨⟨P, hP⟩⟩
  have hEI := exclusive_initialDegree_after_embedding (embedding p) D s hs
    F hF hF0 hzero G hG H hGH
  have hjd : H.totalDegree ≤ p - 3 := by omega
  let c : E → CurveField p := fun P =>
    u ((outsideExclusiveEquiv (embedding p) D H).symm P).val * embedding p (eval P.val.rep H)
  have hc : ∀ P, c P ≠ 0 := exclusive_coefficients_ne_zero (embedding p) D u hu H
  have hrelation := relation_on_exclusive (embedding p) D u (p - 3) H.totalDegree
    hjd H hHhom hrel
  have hrelation' : PowerEvaluationRelation.Relation (representatives (embedding p) E)
      c (p - 3 - s + G.totalDegree) := by
    have heq : p - 3 - H.totalDegree = p - 3 - s + G.totalDegree := by omega
    rw [← heq]
    convert hrelation using 1
    rfl
  obtain ⟨_, _, _, htrunc⟩ := ActualCharacterBounds.full_support_character_bounds
    (representatives (embedding p) E) (representatives_nonzero _ _)
    (representatives_distinct _ _) G.totalDegree hEI c hc _ hrelation'
  have hlo := htrunc G.totalDegree (le_refl G.totalDegree)
  have heq : p - 3 - s + G.totalDegree + 3 - G.totalDegree = p - s := by omega
  simp only [heq, Fintype.card_coe] at hlo
  have hGzero := factor_zero_on_exclusive D F G H hGH hzero
  have hmapG0 : MvPolynomial.map (embedding p) G ≠ 0 := by
    intro hz
    exact hG.ne_zero (MvPolynomial.map_injective (embedding p) (embedding p).injective
      (by simpa only [map_zero] using hz))
  have hzset : zeroSet (embedding p) E (MvPolynomial.map (embedding p) G) = E := by
    apply Finset.filter_eq_self.mpr
    intro Q hQ
    rw [FrobeniusPolarBound.eval_map_at_mapped_point, hGzero Q hQ, map_zero]
  have hcapE := lineCap_subset D E (exclusivePoints_subset D H) ((p - 1) / 2)
    hcap
  have hep : G.totalDegree < p := by omega
  have hpolar := FrobeniusPolarBound.twice_card_le p (embedding p) E hcapE
    (MvPolynomial.map (embedding p) G) G.totalDegree (hGhom.map _) hmapG0 hep
  rw [hzset] at hpolar
  have hupper : E.card ≤ G.totalDegree * (G.totalDegree + p - 1) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    simpa only [mul_comm] using hpolar
  have hebound : p - 2 * s + 1 ≤ G.totalDegree := by
    by_contra hn
    have hlt : G.totalDegree + p - 1 < 2 * (p - s) := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hlt hepos
    nlinarith
  exact ⟨⟨P, hP⟩, hEI, ⟨c, hc, hrelation'⟩, hlo, hupper, hebound⟩

/-- All component assertions hold for any prescribed minimum equation. -/
theorem given_minimum_equation (hp : 11 ≤ p)
    (D : Finset (PlanePoint (ZMod p))) (hcap : LineCap D ((p - 1) / 2))
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) D) s)
    (u : D → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation (representatives (embedding p) D) u (p - 3))
    (hsup : s ≤ (p - 3) / 2)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    Squarefree F ∧ Squarefree (MvPolynomial.map (embedding p) F) ∧
    (∀ G ∈ PlaneCurveFactors.factors F, Irreducible (MvPolynomial.map (embedding p) G)) ∧
    (∑ G ∈ PlaneCurveFactors.factors F, G.totalDegree) = s ∧
    DirectionCurveProposition.ComponentConclusion p s D F := by
  have hsbase := (RationalMinimumEquation.initialDegree_iff (embedding p) D s).mp hs
  have hsq := MinimumEquationReduced.squarefree_of_initialDegree
    (baseRepresentatives D) s hsbase F hF hF0 (fun P => hzero P.val P.property)
  have hsqmap : Squarefree (MvPolynomial.map (embedding p) F) := by
    apply MinimumEquationReduced.squarefree_of_initialDegree (representatives (embedding p) D)
      s hs _ (hF.map (embedding p))
    · intro hz
      exact hF0 (MvPolynomial.map_injective (embedding p) (embedding p).injective
        (by simpa only [map_zero] using hz))
    · intro P
      change eval (fun j => embedding p (P.val.rep j)) (MvPolynomial.map (embedding p) F) = 0
      rw [FrobeniusPolarBound.eval_map_at_mapped_point, hzero P.val P.property, map_zero]
  refine ⟨hsq, hsqmap, ?_, ?_, ?_⟩
  · exact MinimumEquationAbsoluteFactors.factors_absolutely_irreducible
      p D s hsbase F hF hF0 hzero
  · rw [MinimumEquationComponentSets.factors_degree_sum_eq F hF0 hsq, hF.totalDegree hF0]
  · intro G hG H hGH
    exact ⟨MinimumEquationComponentSets.exclusivePoints_eq_componentPoints
      D F G H hF0 hsq hG hGH hzero,
      component_bounds p hp D hcap s hs u hu hrel hsup F hF hF0 hzero G
        (PlaneCurveFactors.factor_irreducible F G hG) H hGH⟩

end Cylinder.ManuscriptCurveComponents
end
