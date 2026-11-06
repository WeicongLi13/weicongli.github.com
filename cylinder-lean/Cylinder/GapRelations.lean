module

public import Cylinder.PlaneGap
public import Cylinder.PowerEvaluationRelation

/-! The full-support relation conclusion of `lem:gap`, derived from the actual
common curve and the proved independent complementary point set. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.GapRelations
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.ReducedGapIdeal Cylinder.PlaneGap Cylinder.HilbertCharacterFormulas
variable {K I : Type*} [Field K] [Fintype I]

theorem relation_after_factor (v : I → Fin 3 → K) (c : I → K) (d j : ℕ)
    (hjd : j ≤ d) (G : PlaneRing K) (hG : G.IsHomogeneous j)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) :
    Cylinder.PowerEvaluationRelation.Relation (outsideRepresentatives v G)
      (fun i => c i.val * eval (v i.val) G) (d - j) := by
  intro F hF
  have hprod : (G * F).IsHomogeneous d := by
    have h := hG.mul hF
    rwa [Nat.add_sub_cancel' hjd] at h
  have hfull := hrel (G * F) hprod
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : I => eval (v i) G ≠ 0)
    (fun i => c i * eval (v i) (G * F))
  have hzero : (∑ i : {i : I // ¬eval (v i) G ≠ 0}, c i.val * eval (v i.val) (G * F)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : eval (v i.val) G = 0 := not_not.mp i.property
    simp only [map_mul, hi, zero_mul, mul_zero]
  rw [hzero, add_zero, hfull] at hsplit
  change (∑ i : {i : I // eval (v i) G ≠ 0},
    (c i.val * eval (v i.val) G) * eval (v i.val) F) = 0
  convert hsplit using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  ring

theorem relation_zero_of_surjective (v : I → Fin 3 → K) (c : I → K) (d : ℕ)
    (hsurj : Function.Surjective (evaluationMap v d))
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) : ∀ i, c i = 0 := by
  intro i
  obtain ⟨F, hF⟩ := hsurj (Pi.single i (1 : K))
  have h := hrel F.val F.property
  have hvals (k : I) : eval (v k) F.val = (Pi.single i (1 : K) : I → K) k := congrFun hF k
  simpa [hvals, Pi.single_apply] using h

theorem full_support_gap_bound [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s j : ℕ) (hs : InitialDegree v s) (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1))
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : Cylinder.PowerEvaluationRelation.Relation v c d) : d + 2 ≤ numericalCharacter v j := by
  by_contra hn
  obtain ⟨G, _, hG, _, hY, _, hind⟩ := gap_data v hv hsep s j hs hj0 hjs hgap
  have hq := (Cylinder.NumericalGapEvaluation.actual_gap_plateau v hv hsep s j hs hj0 hjs hgap).1
  have hjd : j ≤ d := by omega
  have hrelY := relation_after_factor v c d j hjd G hG hrel
  have hzero := relation_zero_of_surjective (outsideRepresentatives v G)
    (fun i => c i.val * eval (v i.val) G) (d - j)
    (hind (d - j) (by omega)) hrelY
  let i : Outside v G := Classical.choice hY
  exact (mul_ne_zero (hc i.val) i.property) (hzero i)

end Cylinder.GapRelations
end
