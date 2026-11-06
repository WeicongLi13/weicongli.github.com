module

public import Cylinder.BMMConicBlockSums
public import Cylinder.BMMNormalizationUniqueness

/-! Zero sums in every conic block use one fixed normalization, even
when its anchor differs from the point selecting the block. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFixedNormalizationBlockSums

set_option backward.isDefEq.respectTransparency false

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BlackProjectionRationalLines
open Cylinder.BMMBlackLineBlocks Cylinder.BMMBlackLinePointSets
open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData
open Cylinder.BMMNormalizedGeometry Cylinder.ConicNormalizedBlockVectors
open Cylinder.BMMConicBlockSums Cylinder.BMMNormalizationUniqueness

variable {K : Type*} [Field K]

def fiberVectorSum (N : NormalizedSystem K) (l : Fin 3 → K) (h : K) : Fin 3 → K :=
  ∑ P ∈ whiteFiber N l h, N.E P

theorem pointFiber_sum_eq (N : NormalizedSystem K) (l : Fin 3 → K) (h : K) :
    (∑ P : pointFiber N l h, N.E (fiberWhite N l h P)) = fiberVectorSum N l h := by
  calc
    _ = ∑ P : whiteFiber N l h, N.E P.val := by
      apply Fintype.sum_equiv (pointFiberEquiv N l h).symm
      intro P
      apply congrArg N.E
      exact Subtype.ext (pointFiberEquiv_symm_val N l h P).symm
    _ = _ := Finset.sum_coe_sort _ _

theorem fixed_normalization_block_sum_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : 3 ≤ (lineBlacks N l).card) (anchor : N.W) :
    fiberVectorSum N l (height N l anchor) +
      fiberVectorSum N l (-height N l anchor) = 0 := by
  let A : Configuration (ZMod p) := ⟨N.W, N.B, N.arc, N.disjoint, N.blocks, N.card⟩
  let M := normalizedSystem A anchor
  obtain ⟨c, hc, hE⟩ := change_anchor_is_scalar N anchor
  change ∀ P : N.W, M.E P = c • N.E P at hE
  have hheight (P : N.W) : height M l P = c * height N l P := by
    change dotMap l (M.E P) = c * dotMap l (N.E P)
    rw [hE P, map_smul, smul_eq_mul]
  have hpos : whiteFiber M l (height M l anchor) = whiteFiber N l (height N l anchor) := by
    ext P
    change P ∈ whiteFiber M l (height M l anchor) ↔
      P ∈ whiteFiber N l (height N l anchor)
    simp only [whiteFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change height M l P = height M l anchor ↔ height N l P = height N l anchor
    rw [hheight P, hheight anchor]
    exact ⟨mul_left_cancel₀ hc, congrArg (fun x => c * x)⟩
  have hneg : whiteFiber M l (-height M l anchor) = whiteFiber N l (-height N l anchor) := by
    ext P
    change P ∈ whiteFiber M l (-height M l anchor) ↔
      P ∈ whiteFiber N l (-height N l anchor)
    simp only [whiteFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change height M l P = -height M l anchor ↔ height N l P = -height N l anchor
    rw [hheight P, hheight anchor, ← mul_neg]
    exact ⟨mul_left_cancel₀ hc, congrArg (fun x => c * x)⟩
  have hposSum : fiberVectorSum M l (height M l anchor) =
      c • fiberVectorSum N l (height N l anchor) := by
    simp only [fiberVectorSum, hpos, hE, Finset.smul_sum]
    rfl
  have hnegSum : fiberVectorSum M l (-height M l anchor) =
      c • fiberVectorSum N l (-height N l anchor) := by
    simp only [fiberVectorSum, hneg, hE, Finset.smul_sum]
    rfl
  have hcard : (blackLine A l).card = (lineBlacks N l).card := by
    simp only [Cylinder.BMMActualBlackLineData.blackLine, A]
    rw [← pointLineBlacks_eq_filter, pointLineBlacks_card]
  have hsum := actual_prime_block_sum_zero p hp A anchor l hl (by omega)
  change (∑ P : pointFiber M l (height M l anchor), M.E (fiberWhite M l _ P)) +
    (∑ P : pointFiber M l (-height M l anchor), M.E (fiberWhite M l _ P)) = 0 at hsum
  rw [pointFiber_sum_eq, pointFiber_sum_eq, hposSum, hnegSum, ← smul_add] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left hc

end Cylinder.BMMFixedNormalizationBlockSums

end
