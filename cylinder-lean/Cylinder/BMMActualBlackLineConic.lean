module

public import Cylinder.BMMBlackLineConic
public import Cylinder.BMMActualBlackLineData

/-! The actual fixed-black-line blocks lie on a genuine conic, using only
the original configuration and the explicit characteristic bound on the
black-line cardinality. No projection matching or conic is an input. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMActualBlackLineConic

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData

variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
theorem characteristic_two_ne_zero (p : ℕ) [CharP K p] (hp : 3 ≤ p) : (2 : K) ≠ 0 := by
  intro hz
  have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem conic_on_actual_blocks (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 ≤ p)
    (A : Configuration K) (anchor : A.W) (l : Fin 3 → K) (hl : l ≠ 0)
    (hm : 2 ≤ (blackLine A l).card) (hmp : (blackLine A l).card ≤ p) :
    ∃ Q : MvPolynomial (Fin 3) K, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧
      ∀ P ∈ positiveBlock A anchor l ∪ negativeBlock A anchor l, eval P.rep Q = 0 := by
  have htwo := characteristic_two_ne_zero (K := K) p hp
  obtain ⟨hXcard, hYcard⟩ := actual_block_cards A anchor l hl htwo hm
  obtain ⟨hdisj, _hXC, _hYC⟩ := actual_blocks_disjoint A anchor l hl htwo hm
  obtain ⟨hXoff, hYoff⟩ := actual_blocks_off_line A anchor l hl hm
  apply BMMBlackLineConic.conic_of_collinear_matchings p l hl
    (positiveBlock A anchor l) (negativeBlock A anchor l) (blackLine A l)
    hdisj hXcard hYcard (Finset.card_pos.mp (by omega)) hmp hXoff hYoff
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · intro R
    exact ⟨blockMatching A anchor l R, blockMatching_collinear A anchor l R⟩

end Cylinder.BMMActualBlackLineConic

end
