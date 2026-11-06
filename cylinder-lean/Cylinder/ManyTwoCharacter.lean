module

public import Cylinder.ManyTwoStaircase
public import Cylinder.ActualComponentCharacter
public import Cylinder.DirectionCurveComponentCounting

/-! The staircase sum for the actual numerical character of a literal
exclusive component of the black direction curve. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ManyTwoCharacter
open MvPolynomial Finset
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition
open Cylinder.MinimumEquationComponents Cylinder.MinimumEquationComponentSets
open Cylinder.DirectionCurveComponentCounting Cylinder.RationalPlanePointModel
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas
open Cylinder.ComponentCharacterNumeric Cylinder.PlaneCurveFactors
variable (p : ℕ) [Fact p.Prime]

def componentIncrement {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (s : ℕ) (F G : MvPolynomial (Fin 3) (ZMod p)) (j : ℕ) : ℕ :=
  increment (numericalCharacter (representatives (embedding p)
    (componentPoints (directionSet p S b hb) F G))) (p - 3 - s + G.totalDegree) j

omit [Fact p.Prime] in
theorem component_degree_arithmetic (s e : ℕ) (hp : 3 ≤ p)
    (hs : s ≤ (p - 3) / 2) (he : e ≤ s) :
    2 * e ≤ p - 3 - s + e ∧ (p - 3 - s + e) + 3 - e = p - s := by
  omega

theorem component_increment_data {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (hp : 3 ≤ p) (s : ℕ) (hs : s ≤ (p - 3) / 2)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hG : G ∈ factors F) (hGirr : Irreducible (MvPolynomial.map (embedding p) G))
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) :
    (∀ j, j + 1 < G.totalDegree → componentIncrement p hb s F G j ≤
      componentIncrement p hb s F G (j + 1)) ∧
    (∑ j ∈ range G.totalDegree, componentIncrement p hb s F G j) = componentExcess p hb s F G := by
  classical
  let : DecidableEq (ZMod p) := Classical.decEq _
  let E := componentPoints (directionSet p S b hb) F G
  obtain ⟨H, hFH⟩ := factor_dvd F G hG
  have hdata := hcomp G hG H hFH
  have heq : exclusivePoints (directionSet p S b hb) H = E := hdata.1
  have hEnon : E.Nonempty := by rw [← heq]; exact hdata.2.1
  let : Nonempty E := hEnon.coe_sort
  have hinit : InitialDegree (representatives (embedding p) E) G.totalDegree := by
    rw [← heq]
    exact hdata.2.2.1
  have hfull : ∃ c : E → CurveField p, (∀ i, c i ≠ 0) ∧
      PowerEvaluationRelation.Relation (representatives (embedding p) E) c
        (p - 3 - s + G.totalDegree) := by
    rw [← heq]
    exact hdata.2.2.2.1
  obtain ⟨c, hc, hrel⟩ := hfull
  have hGhom := Cylinder.HomogeneousFactors.homogeneous_of_dvd G F s hF hF0 (factor_dvd F G hG)
  have hGvan : ∀ P : E, eval (representatives (embedding p) E P) (MvPolynomial.map (embedding p) G) = 0 := by
    intro P
    have hm : P.val ∈ E := P.property
    dsimp only [E, componentPoints] at hm
    rw [Finset.mem_filter] at hm
    have hz : eval P.val.rep G = 0 := hm.2.1
    rw [eval_mapped_cofactor, hz, map_zero]
  have he : G.totalDegree ≤ s := by
    have h := totalDegree_le_of_dvd_of_isDomain (factor_dvd F G hG) hF0
    rwa [hF.totalDegree hF0] at h
  have harith := component_degree_arithmetic p s G.totalDegree hp hs he
  have hcharacter := ActualComponentCharacter.character_increments
    (representatives (embedding p) E) (representatives_nonzero _ E) (representatives_distinct _ E)
    (MvPolynomial.map (embedding p) G) G.totalDegree (hGhom.map _) hGirr hGvan hinit c hc
    (p - 3 - s + G.totalDegree) harith.1 hrel
  refine ⟨fun j hj => (hcharacter.2.2.1 j hj).1, ?_⟩
  change (∑ j ∈ range G.totalDegree, increment (numericalCharacter (representatives (embedding p) E))
    (p - 3 - s + G.totalDegree) j) = _
  rw [hcharacter.2.2.2, harith.2]
  simp only [Fintype.card_coe, componentExcess, E]

theorem component_staircase_bound {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (hp : 3 ≤ p) (s : ℕ) (hs : s ≤ (p - 3) / 2)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hG : G ∈ factors F) (hGirr : Irreducible (MvPolynomial.map (embedding p) G))
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (m : ℕ) (hme : 4 * m + 2 < G.totalDegree)
    (hstair : ∀ j, 1 ≤ j → j ≤ m → j ≤ componentIncrement p hb s F G (3 * j)) :
    2 * m * G.totalDegree ≤ 2 * componentExcess p hb s F G + 3 * m * (m + 1) := by
  obtain ⟨hinc, hsum⟩ := component_increment_data p hb hp s hs F G hF hF0 hG hGirr hcomp
  have h := ManyTwoStaircase.staircase_bound (componentIncrement p hb s F G)
    G.totalDegree m (by omega) hinc hstair
  rw [hsum] at h
  exact h

end Cylinder.ManyTwoCharacter
end
