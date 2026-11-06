module

public import Cylinder.BMMFrameAxisSlices
public import Cylinder.BMMBothThreeImpossible
public import Cylinder.BMMBothFourImpossible
public import Cylinder.WhitePlaneBMMCondition

/-! The two original cross axes of every actual nonspecial tuple have
respectively three and four black points. All bounds and the exclusions
of equal sizes come from the original prime-field configuration. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMAxisClassification
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMPrimeFourTupleCoordinates Cylinder.BMMCoordinateFibers Cylinder.BMMBlackLineCapFour
open Cylinder.BMMFrameAxisSlices Cylinder.BMMClassificationCounting Cylinder.ProjectiveSecantCounting

theorem actual_axis_classification (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) : AxisClassification N := by
  intro R T
  have hb := prime_axes_card_bounds p hp N T
  have hthree := BMMBothThreeImpossible.prime_not_both_three p hp N T
  have hfour := BMMBothFourImpossible.prime_not_both_four p hp N T
  have hc :
      ((coordinateBlacks N (primeBlackFrame p hp N T) 1).card = 3 ∧
        (coordinateBlacks N (primeBlackFrame p hp N T) 0).card = 4) ∨
      ((coordinateBlacks N (primeBlackFrame p hp N T) 1).card = 4 ∧
        (coordinateBlacks N (primeBlackFrame p hp N T) 0).card = 3) := by omega
  change ((lineSlice N.B (firstLine N T)).card = 3 ∧
      (lineSlice N.B (secondLine N T)).card = 4) ∨
    ((lineSlice N.B (firstLine N T)).card = 4 ∧
      (lineSlice N.B (secondLine N T)).card = 3)
  rw [first_axis_card N T (normalized_black_line_cap_four p hp N),
    second_axis_card N T (normalized_black_line_cap_four p hp N)]
  exact hc

theorem white_card_le_four_of_recovery (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (N : NormalizedSystem (ZMod p)) (hrecover : AxisRecovery N) : N.W.card ≤ 4 :=
  white_card_le_four_of_local_structure p hp N (actual_axis_classification p (by omega) N) hrecover

theorem bmm_classification_of_recovery (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hrecover : ∀ N : NormalizedSystem (ZMod p), AxisRecovery N) :
    Cylinder.WhitePlaneBMMCondition.BMMClassification p := by
  intro W B hW hd hb hc hmin
  let A : Cylinder.BMMActualCoefficients.Configuration (ZMod p) := ⟨W, B, hW, hd, hb, hc⟩
  have hnon : A.W.Nonempty := Finset.card_pos.mp (by change 0 < W.card; omega)
  let anchor : A.W := ⟨hnon.choose, hnon.choose_spec⟩
  let N := Cylinder.BMMNormalizedGeometry.normalizedSystem A anchor
  exact configuration_card_two_or_four_of_local_structure p hp A anchor
    (actual_axis_classification p (by omega) N) (hrecover N) hmin

end Cylinder.BMMAxisClassification
end
