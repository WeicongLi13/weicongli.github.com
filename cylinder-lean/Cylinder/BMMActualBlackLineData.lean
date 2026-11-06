module

public import Cylinder.BMMNormalizedGeometry
public import Cylinder.BMMBlackLinePointSets
public import Cylinder.BMMBlackLinePartition

/-! Fixed-black-line block data derived solely from the actual BMM arc
configuration. The Segre lemma supplies the normalized vectors internally. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMActualBlackLineData

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMActualCoefficients Cylinder.BMMNormalizedGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMBlackLinePointSets Cylinder.BMMBlackLinePartition

variable {K : Type*} [Field K]

def blackLine (A : Configuration K) (l : Fin 3 → K) : Finset (PlanePoint K) :=
  A.B.filter (fun R => dot l R.rep = 0)

def positiveBlock (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) : Finset (PlanePoint K) :=
  pointFiber (normalizedSystem A anchor) l (height (normalizedSystem A anchor) l anchor)

def negativeBlock (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) : Finset (PlanePoint K) :=
  pointFiber (normalizedSystem A anchor) l (-height (normalizedSystem A anchor) l anchor)

theorem normalized_line_points (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) :
    pointLineBlacks (normalizedSystem A anchor) l = blackLine A l := by
  rw [pointLineBlacks_eq_filter]
  rfl

theorem normalized_line_card (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) :
    (lineBlacks (normalizedSystem A anchor) l).card = (blackLine A l).card := by
  rw [← pointLineBlacks_card, normalized_line_points]

def blockMatching (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (R : blackLine A l) :
    positiveBlock A anchor l ≃ negativeBlock A anchor l :=
  pointMatching (normalizedSystem A anchor) l (height (normalizedSystem A anchor) l anchor)
    ⟨R.val, by rw [normalized_line_points]; exact R.property⟩

theorem blockMatching_collinear (A : Configuration K) (anchor : A.W) (l : Fin 3 → K)
    (R : blackLine A l) (P : positiveBlock A anchor l) :
    Collinear P.val (blockMatching A anchor l R P).val R.val :=
  pointMatching_collinear (normalizedSystem A anchor) l (height (normalizedSystem A anchor) l anchor)
    ⟨R.val, by rw [normalized_line_points]; exact R.property⟩ P

theorem actual_block_cards (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (blackLine A l).card) :
    (positiveBlock A anchor l).card = (blackLine A l).card ∧
    (negativeBlock A anchor l).card = (blackLine A l).card := by
  have hm' : 2 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  simpa only [positiveBlock, negativeBlock, normalized_line_points] using
    block_point_cards (normalizedSystem A anchor) l hl htwo hm' anchor

theorem actual_blocks_disjoint (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (blackLine A l).card) :
    Disjoint (positiveBlock A anchor l) (negativeBlock A anchor l) ∧
    Disjoint (positiveBlock A anchor l) (blackLine A l) ∧
    Disjoint (negativeBlock A anchor l) (blackLine A l) := by
  have hm' : 2 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  refine ⟨pointFibers_disjoint (normalizedSystem A anchor) l _
    (height_ne_neg (normalizedSystem A anchor) l anchor htwo
      (white_height_ne_zero (normalizedSystem A anchor) l hl hm' anchor)), ?_, ?_⟩
  · rw [← normalized_line_points A anchor l]
    exact pointFiber_black_disjoint (normalizedSystem A anchor) l _
  · rw [← normalized_line_points A anchor l]
    exact pointFiber_black_disjoint (normalizedSystem A anchor) l _

theorem actual_blocks_union_card (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (blackLine A l).card) :
    (positiveBlock A anchor l ∪ negativeBlock A anchor l).card = 2 * (blackLine A l).card := by
  have hm' : 2 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  simpa only [positiveBlock, negativeBlock, normalized_line_points] using
    blocks_union_card (normalizedSystem A anchor) l hl htwo hm' anchor

theorem actual_blocks_arc (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) :
    LineCap (positiveBlock A anchor l ∪ negativeBlock A anchor l) 2 :=
  blocks_union_arc (normalizedSystem A anchor) l _

theorem actual_blocks_off_line (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (hl : l ≠ 0)
    (hm : 2 ≤ (blackLine A l).card) :
    (∀ P ∈ positiveBlock A anchor l, dot l P.rep ≠ 0) ∧
    (∀ P ∈ negativeBlock A anchor l, dot l P.rep ≠ 0) := by
  have hm' : 2 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  exact ⟨block_points_off_line (normalizedSystem A anchor) l hl hm' _,
    block_points_off_line (normalizedSystem A anchor) l hl hm' _⟩

theorem actual_cross_secants_blocked (A : Configuration K) (anchor : A.W) (l : Fin 3 → K)
    (hl : l ≠ 0) (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (blackLine A l).card) :
    ∀ P ∈ positiveBlock A anchor l, ∀ Q ∈ negativeBlock A anchor l,
      ∃ R ∈ blackLine A l, Collinear P Q R := by
  have hm' : 2 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  simpa only [positiveBlock, negativeBlock, normalized_line_points] using
    point_cross_secant_blocked (normalizedSystem A anchor) l anchor htwo
      (white_height_ne_zero (normalizedSystem A anchor) l hl hm' anchor)

theorem actual_line_card_dvd_half_white (A : Configuration K) (anchor : A.W) (l : Fin 3 → K)
    (hl : l ≠ 0) (htwo : (2 : K) ≠ 0) (hm : 1 ≤ (blackLine A l).card)
    (n : ℕ) (hn : A.W.card = 2 * n) : (blackLine A l).card ∣ n := by
  have hm' : 1 ≤ (lineBlacks (normalizedSystem A anchor) l).card := by rwa [normalized_line_card]
  have hdiv := line_card_dvd_half_white (normalizedSystem A anchor) l hl htwo hm' n hn
  rwa [normalized_line_card] at hdiv

end Cylinder.BMMActualBlackLineData

end
