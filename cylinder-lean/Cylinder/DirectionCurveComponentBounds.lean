module

public import Cylinder.DirectionCurveBounds
public import Cylinder.MinimumEquationComponents

/-!
The component estimates in the direction-curve proposition. The point
set of a component is the actual filter where its cofactor is nonzero.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.DirectionCurveComponentBounds

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.PlaneBinaryReduction Cylinder.RationalMinimumEquation
open Cylinder.MinimumEquationComponents Cylinder.DirectionCurveBounds

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem lineCap_subset {K : Type*} [Field K] (D E : Finset (PlanePoint K))
    (hED : E ⊆ D) (a : ℕ) (hcap : LineCap D a) : LineCap E a := by
  intro c hc
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hED)).trans (hcap c hc)

theorem component_bounds {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (u : directionSet p S b hb → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3))
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (G : MvPolynomial (Fin 3) (ZMod p)) (hG : Irreducible G)
    (H : MvPolynomial (Fin 3) (ZMod p)) (hGH : F = G * H) :
    (exclusivePoints (directionSet p S b hb) H).Nonempty ∧
      InitialDegree (representatives (embedding p)
        (exclusivePoints (directionSet p S b hb) H)) G.totalDegree ∧
      (∃ c : exclusivePoints (directionSet p S b hb) H → CurveField p,
        (∀ i, c i ≠ 0) ∧ PowerEvaluationRelation.Relation
          (representatives (embedding p) (exclusivePoints (directionSet p S b hb) H))
          c (p - 3 - s + G.totalDegree)) ∧
      G.totalDegree * (p - s) ≤ (exclusivePoints (directionSet p S b hb) H).card ∧
      (exclusivePoints (directionSet p S b hb) H).card ≤
        G.totalDegree * (G.totalDegree + p - 1) / 2 ∧
      p - 2 * s + 1 ≤ G.totalDegree := by
  let D := directionSet p S b hb
  let E := exclusivePoints D H
  have hsbase := (RationalMinimumEquation.initialDegree_iff (embedding p) D s).mp hs
  obtain ⟨hH0, hGhom, hHhom, hdeg, hepos⟩ := cofactor_data D s F hF hF0 G hG H hGH
  have hE := exclusive_nonempty D s hsbase F hF hF0 G hG H hGH
  obtain ⟨P, hP⟩ := hE
  let : Nonempty E := ⟨⟨P, hP⟩⟩
  have hEI := exclusive_initialDegree_after_embedding (embedding p) D s hs
    F hF hF0 hzero G hG H hGH
  have hsup := initial_degree_upper p hp hcard hS hnon hb s hs u hu hrel
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
    (direction_lineCap p hcard hS hnon hb)
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

theorem exists_equation_with_component_bounds {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (u : directionSet p S b hb → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3)) :
    ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
      (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧ Squarefree F ∧
      Squarefree (MvPolynomial.map (embedding p) F) ∧
      (∀ G ∈ PlaneCurveFactors.factors F,
        Irreducible (MvPolynomial.map (embedding p) G)) ∧
      ∀ G ∈ PlaneCurveFactors.factors F, p - 2 * s + 1 ≤ G.totalDegree := by
  obtain ⟨F, hF, hF0, hzero, hsq, hsqmap, habs⟩ :=
    MinimumEquationAbsoluteFactors.exists_reduced_base_equation_with_absolute_factors
      p (directionSet p S b hb) s hs
  refine ⟨F, hF, hF0, hzero, hsq, hsqmap, habs, ?_⟩
  intro G hG
  obtain ⟨H, hGH⟩ := PlaneCurveFactors.factor_dvd F G hG
  exact (component_bounds p hp hcard hS hnon hb s hs u hu hrel F hF hF0 hzero G
    (PlaneCurveFactors.factor_irreducible F G hG) H hGH).2.2.2.2.2

theorem direction_curve_bounds {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (u : directionSet p S b hb → CurveField p) (hu : ∀ i, u i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (representatives (embedding p) (directionSet p S b hb)) u (p - 3)) :
    DirectionExcess.threshold p ≤ s ∧ s ≤ (p - 3) / 2 ∧
      s * (p - s) ≤ (directionSet p S b hb).card ∧
      (directionSet p S b hb).card ≤ (whitePoints p S).card / 2 ∧
      (directionSet p S b hb).card ≤ s * (s + p - 1) / 2 ∧
      ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
        (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧ Squarefree F ∧
        Squarefree (MvPolynomial.map (embedding p) F) ∧
        (∀ G ∈ PlaneCurveFactors.factors F,
          Irreducible (MvPolynomial.map (embedding p) G)) ∧
        ∀ G ∈ PlaneCurveFactors.factors F, p - 2 * s + 1 ≤ G.totalDegree := by
  obtain ⟨hlo, hhi, hkl, hkn, hkp⟩ := numerical_bounds p hp hcard hS hnon hb s hs u hu hrel
  exact ⟨hlo, hhi, hkl, hkn, hkp,
    exists_equation_with_component_bounds p hp hcard hS hnon hb s hs u hu hrel⟩

end Cylinder.DirectionCurveComponentBounds

end
