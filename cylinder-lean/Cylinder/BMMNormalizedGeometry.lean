module

public import Cylinder.BMMBlackLineBlocks
public import Cylinder.BMMSpecialFourTuple

/-! Build the normalized system from the original arc and blocker data,
using the actual Segre construction once for all white points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMNormalizedGeometry

open Cylinder.BMMActualCoefficients Cylinder.BMMSegreLemma
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple

variable {K : Type*} [Field K]

def normalizedSystem (A : Configuration K) (anchor : A.W) : NormalizedSystem K where
  W := A.W
  B := A.B
  arc := A.arc
  disjoint := A.disjoint
  blocks := A.blocks
  card := A.card
  E := Classical.choose (actual_normalized_vector_data A anchor)
  representatives := (Classical.choose_spec (actual_normalized_vector_data A anchor)).1
  sums := (Classical.choose_spec (actual_normalized_vector_data A anchor)).2

theorem normalized_representatives (A : Configuration K) (anchor : A.W) :
    ∀ P, ∃ α : K, α ≠ 0 ∧ (normalizedSystem A anchor).E P = α • P.val.rep :=
  (normalizedSystem A anchor).representatives

theorem normalized_sums (A : Configuration K) (anchor : A.W) (P Q : A.W) (hPQ : P ≠ Q) :
    ∃ β : K, β ≠ 0 ∧ (normalizedSystem A anchor).E P + (normalizedSystem A anchor).E Q =
      β • (Cylinder.BMMActualCoefficients.blocker A P Q hPQ).val.rep :=
  (normalizedSystem A anchor).sums P Q hPQ

theorem nonspecial_fourtuple (A : Configuration K) (anchor : A.W)
    (htwo : (2 : K) ≠ 0) (hlarge : 4 < A.W.card) (R : A.B) :
    Nonempty (FourTuple A (normalizedSystem A anchor).E R) :=
  exists_actual_nonspecial_fourtuple A (normalizedSystem A anchor).E
    (normalized_representatives A anchor) htwo hlarge R

end Cylinder.BMMNormalizedGeometry

end
