module

public import Cylinder.BMMFinitePlaneArcBound
public import Cylinder.WhitePlaneBMMCondition

/-! The two smallest prime planes need only the true arc bound and
the blocker matching parity. -/

@[expose] public section
noncomputable section

namespace Cylinder.BMMPrimeSmall

open Cylinder.BMMFinitePlaneArcBound Cylinder.BMMMatchingParity
open Cylinder.WhitePlaneBMMCondition

variable (p : ℕ) [Fact p.Prime]

theorem bmm_of_prime_le_three (hp : p ≤ 3) : BMMClassification p := by
  intro W B hW hdisj hblocks hcard hmin
  have hbound := arc_card_le_prime_add_two p W hW
  obtain ⟨n, hn⟩ := white_card_even W B hW hdisj hblocks hcard hmin
  omega

theorem prime_three_nonzero (hp : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro hz
  have hdiv := (ZMod.natCast_eq_zero_iff 3 p).mp hz
  have hle := Nat.le_of_dvd (by decide : 0 < 3) hdiv
  omega

end Cylinder.BMMPrimeSmall

end
