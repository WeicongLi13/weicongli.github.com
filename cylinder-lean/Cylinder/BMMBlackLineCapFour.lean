module

public import Cylinder.BMMConicBlockCosets
public import Cylinder.NormalizedHyperbolaCosetObstruction
public import Cylinder.BMMActualBlackLineConic

/-! BMM Lemma 5 for the actual original prime-field configuration.
The conic, coset parameters, representative identities, and black-pair
membership are proved by the preceding genuine geometric interfaces. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlackLineCapFour

open Cylinder.RationalPlaneLine Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData
open Cylinder.BMMNormalizedGeometry Cylinder.BMMBlackLineBlocks Cylinder.ConicNormalizedBlockVectors
open Cylinder.ProjectiveFieldEmbedding Cylinder.ConicRootPairsGeometry
open Cylinder.BMMConicBlockCosets Cylinder.NormalizedHyperbolaCosetObstruction

variable (p : ℕ) [Fact p.Prime]

theorem actual_black_line_card_le_four (hp : 3 ≤ p) (A : Configuration (ZMod p))
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) : (blackLine A l).card ≤ 4 := by
  by_cases hm : 3 ≤ (blackLine A l).card
  · have hW : A.W.Nonempty := Finset.card_pos.mp (by have hcard := A.card; omega)
    let anchor : A.W := ⟨hW.choose, hW.choose_spec⟩
    let K := AlgebraicClosure (ZMod p)
    let ι := ProductEvaluationRelation.primeEmbedding p (K := K)
    let N := normalizedSystem A anchor
    let h := height N l anchor
    obtain ⟨D⟩ := exists_actual_block_coset_data (K := K) p hp A anchor l hl hm
    let : Finite D.H := D.finite
    have htwo : (2 : K) ≠ 0 := BMMActualBlackLineConic.characteristic_two_ne_zero p hp
    have hbound := subgroup_coset_card_le_four N ι D.g D.H D.a D.c D.c_ne htwo
      (fun t => fiberWhite N l h (D.posEquiv.symm t)) (by
        intro t
        simpa only [D.posEquiv.apply_symm_apply] using D.pos_vectors (D.posEquiv.symm t))
    rwa [D.card] at hbound
  · omega

theorem actual_black_line_cap_four (hp : 3 ≤ p) (A : Configuration (ZMod p)) : LineCap A.B 4 := by
  intro l hl
  exact actual_black_line_card_le_four p hp A l hl

theorem normalized_black_line_cap_four (hp : 3 ≤ p) (N : NormalizedSystem (ZMod p)) :
    LineCap N.B 4 :=
  actual_black_line_cap_four p hp ⟨N.W, N.B, N.arc, N.disjoint, N.blocks, N.card⟩

end Cylinder.BMMBlackLineCapFour

end
