module

public import Cylinder.BMMBlackLineConicDescent
public import Cylinder.BMMFinitePlaneArcBound
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The literal prime-field fixed-black-line blocks lie on a nonzero
prime-field conic. The bound m < p is proved from the original arc geometry,
and the extension-field conic is descended to the actual original points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMPrimeBlackLineConic

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData
open Cylinder.BMMFinitePlaneArcBound

variable (p : ℕ) [Fact p.Prime]

theorem conic_on_prime_blocks (hp : 3 ≤ p) (A : Configuration (ZMod p)) (anchor : A.W)
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) (hm : 2 ≤ (blackLine A l).card) :
    ∃ Q : MvPolynomial (Fin 3) (ZMod p), Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧
      ∀ P ∈ positiveBlock A anchor l ∪ negativeBlock A anchor l, eval P.rep Q = 0 := by
  let : DecidableEq (ZMod p) := Classical.decEq _
  have htwo := prime_two_nonzero p hp
  obtain ⟨hXcard, hYcard⟩ := actual_block_cards A anchor l hl htwo hm
  obtain ⟨hdisj, _hXC, _hYC⟩ := actual_blocks_disjoint A anchor l hl htwo hm
  obtain ⟨hXoff, hYoff⟩ := actual_blocks_off_line A anchor l hl hm
  have hCp := (actual_black_line_card_lt_prime p A hp l hl).le
  apply BMMBlackLineConicDescent.conic_of_base_collinear_matchings (K := AlgebraicClosure (ZMod p))
    p l hl (positiveBlock A anchor l) (negativeBlock A anchor l) (blackLine A l)
    hdisj hXcard hYcard (Finset.card_pos.mp (by omega)) hCp hXoff hYoff
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · intro R
    exact ⟨blockMatching A anchor l R, blockMatching_collinear A anchor l R⟩

end Cylinder.BMMPrimeBlackLineConic

end
