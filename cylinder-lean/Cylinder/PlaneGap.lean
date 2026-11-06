module

public import Cylinder.ReducedGapIdeal
public import Cylinder.PlaneHilbertStability
public import Cylinder.NumericalGapEvaluation

/-!
# A numerical-character gap for actual reduced plane points

The common curve is supplied by the saturated ideal plateau theorem. The
points outside it are actual indices, and their independence is proved as
surjectivity of their homogeneous evaluation map.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.PlaneGap
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open Cylinder.ReducedGapIdeal Cylinder.HilbertCharacterFormulas Cylinder.NumericCharacterSequence
open Cylinder.NumericalIdealFormula Cylinder.NumericalGapEvaluation
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

def Inside (v : I → Fin 3 → K) (G : PlaneRing K) := {i : I // eval (v i) G = 0}

instance inside_fintype (v : I → Fin 3 → K) (G : PlaneRing K) : Fintype (Inside v G) := by
  unfold Inside
  infer_instance

set_option backward.isDefEq.respectTransparency false in
omit [Nonempty I] [Infinite K] in
theorem evaluationMap_surjective_of_hilbert_eq_card (v : I → Fin 3 → K) (d : ℕ)
    (hH : hilbert v d = Fintype.card I) : Function.Surjective (evaluationMap v d) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [hilbert, evaluationSpace, Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using hH

theorem common_curve_of_gap (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s j : ℕ) (hs : InitialDegree v s)
    (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1)) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous j ∧ G.totalDegree = j ∧
      ∀ d P, P.IsHomogeneous d → P ∈ (vanishingIdeal v).toIdeal →
        d ≤ numericalCharacter v j + 1 → G ∣ P := by
  obtain ⟨hqs, hq, hq1⟩ := actual_gap_plateau v hv hsep s j hs hj0 hjs hgap
  have hH : Cylinder.PlanePlateau.quotientHilbert (vanishingIdeal v).toIdeal = hilbert v :=
    funext (quotientHilbert_eq_hilbert v)
  apply Cylinder.PlanePlateauTheorem.plane_plateau (vanishingIdeal v).toIdeal
    (vanishingIdeal_saturated v hv) s (numericalCharacter v j) j (initialDegree_ideal v s hs)
    (by omega) hj0
  · rw [hH]
    exact hq
  · rw [hH]
    exact hq1

omit [Infinite K] [Fintype I] [Nonempty I] in
theorem outside_nonempty (v : I → Fin 3 → K) (s j : ℕ) (hs : InitialDegree v s)
    (hjs : j < s) (G : PlaneRing K) (hG0 : G ≠ 0) (hG : G.IsHomogeneous j) :
    Nonempty (Outside v G) := by
  by_contra hn
  have hall : ∀ i, eval (v i) G = 0 := by
    intro i
    by_contra hi
    exact hn ⟨⟨i, hi⟩⟩
  have hm : (⟨G, hG⟩ : Forms K j) ∈ idealPiece v j :=
    (homogeneous_mem_vanishingIdeal v G j hG).mpr hall
  rw [hs.2 j hjs] at hm
  have hz : (⟨G, hG⟩ : Forms K j) = 0 := by simpa using hm
  exact hG0 (congrArg Subtype.val hz)

omit [Nonempty I] in
theorem independence_of_common_factor (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (q j : ℕ) (hjq : j < q)
    (hΔ : firstDifference (hilbert v) q = j) (G : PlaneRing K)
    (hG0 : G ≠ 0) (hG : G.IsHomogeneous j) (hdegree : G.totalDegree = j)
    (hdiv : ∀ d P, P.IsHomogeneous d → P ∈ (vanishingIdeal v).toIdeal → d ≤ q + 1 → G ∣ P) :
    ∀ w, q - j - 1 ≤ w →
      hilbert (outsideRepresentatives v G) w = Fintype.card (Outside v G) := by
  let t := q - j - 1
  let Y := outsideRepresentatives v G
  have hq0 : q - 1 = t + j := by dsimp [t]; omega
  have hq1 : q = (t + 1) + j := by dsimp [t]; omega
  have hr0 := factor_piece_dimension v G j t hG hG0 hdegree
    (fun P hp hpi => hdiv (t + j) P hp hpi (by omega))
  have hr1 := factor_piece_dimension v G j (t + 1) hG hG0 hdegree
    (fun P hp hpi => hdiv (t + 1 + j) P hp hpi (by omega))
  change finrank K (idealPiece v (t + j)) = finrank K (idealPiece Y t) at hr0
  change finrank K (idealPiece v (t + 1 + j)) = finrank K (idealPiece Y (t + 1)) at hr1
  have hd0 := ideal_piece_dimension v (q - 1)
  have hd1 := ideal_piece_dimension v q
  have hy0 := ideal_piece_dimension Y t
  have hy1 := ideal_piece_dimension Y (t + 1)
  rw [← idealPiece_eq_kernel] at hd0 hd1 hy0 hy1
  rw [hq0, hr0] at hd0
  rw [hq1, hr1] at hd1
  have hf0 := forms_rank_succ (K := K) (q - 1)
  have hf1 := forms_rank_succ (K := K) t
  have hqminus : q - 1 + 1 = q := by omega
  rw [hqminus] at hf0
  have hΔ' : hilbert v q - hilbert v (q - 1) = j := by
    have he : q = (q - 1) + 1 := by omega
    rw [he] at hΔ
    simpa only [firstDifference, ← he] using hΔ
  have hmono := hilbert_monotone v hv (show q - 1 ≤ q by omega)
  have heq : hilbert Y (t + 1) = hilbert Y t := by
    rw [← hq0] at hd0
    rw [← hq1] at hd1
    omega
  exact Cylinder.PlaneHilbertStability.hilbert_eq_card_of_equal_succ Y
    (outside_nonzero v hv G) (outside_distinct v hsep G) t heq

theorem inside_length_of_common_factor (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s j : ℕ) (hs : InitialDegree v s)
    (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1))
    (G : PlaneRing K) (hG0 : G ≠ 0) (hG : G.IsHomogeneous j) (hdegree : G.totalDegree = j)
    (hdiv : ∀ d P, P.IsHomogeneous d → P ∈ (vanishingIdeal v).toIdeal →
      d ≤ numericalCharacter v j + 1 → G ∣ P) :
    Fintype.card (Inside v G) = ∑ i ∈ Finset.range j, (numericalCharacter v i - i) := by
  let q := numericalCharacter v j
  let t := q - j - 1
  obtain ⟨hqs, hΔ, _⟩ := actual_gap_plateau v hv hsep s j hs hj0 hjs hgap
  have hqj : j < q := by dsimp [q]; omega
  have hY := independence_of_common_factor v hv hsep q j hqj hΔ G hG0 hG hdegree hdiv t (le_refl _)
  have hr := factor_piece_dimension v G j t hG hG0 hdegree
    (fun P hp hpi => hdiv (t + j) P hp hpi (by dsimp [t]; omega))
  have hq0 : q - 1 = t + j := by dsimp [t]; omega
  have ht : t + 1 = q - j := by dsimp [t]; omega
  have hd := ideal_piece_dimension v (q - 1)
  have hy := ideal_piece_dimension (outsideRepresentatives v G) t
  rw [← idealPiece_eq_kernel, Cylinder.ActualIdealCharacter.forms_dimension, hq0, hr] at hd
  rw [← idealPiece_eq_kernel, Cylinder.ActualIdealCharacter.forms_dimension, ht, hY] at hy
  have htri := triangular_split q j (by omega : j ≤ q)
  have hcard : Fintype.card (Inside v G) = Fintype.card I - Fintype.card (Outside v G) := by
    simpa only [Inside, Outside, not_not] using
      Fintype.card_subtype_compl (fun i : I => eval (v i) G ≠ 0)
  have hHbound := hilbert_le_card v (q - 1)
  have hhead := head_length_from_defect v hv hsep s j hs hj0 hjs hgap
  change triangular q - triangular (q - j) + (Fintype.card I - hilbert v (q - 1)) =
    ∑ i ∈ Finset.range j, (numericalCharacter v i - i) at hhead
  rw [← hq0] at hd
  rw [show q - 1 + 1 = q by omega] at hd
  have he : Fintype.card (Inside v G) =
      triangular q - triangular (q - j) + (Fintype.card I - hilbert v (q - 1)) := by
    omega
  exact he.trans hhead

theorem gap_data (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s j : ℕ) (hs : InitialDegree v s)
    (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1)) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous j ∧ G.totalDegree = j ∧
      Nonempty (Outside v G) ∧
      Fintype.card (Inside v G) = ∑ i ∈ Finset.range j, (numericalCharacter v i - i) ∧
      ∀ w, numericalCharacter v j - j - 1 ≤ w →
        Function.Surjective (evaluationMap (outsideRepresentatives v G) w) := by
  obtain ⟨G, hG0, hG, hdegree, hdiv⟩ := common_curve_of_gap v hv hsep s j hs hj0 hjs hgap
  obtain ⟨hqs, hΔ, _⟩ := actual_gap_plateau v hv hsep s j hs hj0 hjs hgap
  refine ⟨G, hG0, hG, hdegree, outside_nonempty v s j hs hjs G hG0 hG,
    inside_length_of_common_factor v hv hsep s j hs hj0 hjs hgap G hG0 hG hdegree hdiv, ?_⟩
  intro w hw
  apply evaluationMap_surjective_of_hilbert_eq_card
  exact independence_of_common_factor v hv hsep (numericalCharacter v j) j
    (by omega) hΔ G hG0 hG hdegree hdiv w hw

end Cylinder.PlaneGap
end
