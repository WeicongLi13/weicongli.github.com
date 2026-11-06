module

public import Cylinder.BMMAxisClassification
public import Cylinder.BMMOrientedPairRecovery
public import Cylinder.BMMPrimeSmall

/-! The BMM classification, with the local classification and recovery
inputs discharged by the actual geometric proofs. -/

@[expose] public section

namespace Cylinder.BMMTheorem

theorem bmm_classification (p : ℕ) [Fact p.Prime] :
    Cylinder.WhitePlaneBMMCondition.BMMClassification p := by
  by_cases hp : 5 ≤ p
  · exact Cylinder.BMMAxisClassification.bmm_classification_of_recovery p hp
      (Cylinder.BMMOrientedPairRecovery.prime_axis_recovery p hp)
  · have hp3 : p ≤ 3 := by
      by_contra hnot
      have heq : p = 4 := by omega
      have hprime : Nat.Prime 4 := heq ▸ (Fact.out : Nat.Prime p)
      exact (by decide : ¬ Nat.Prime 4) hprime
    exact Cylinder.BMMPrimeSmall.bmm_of_prime_le_three p hp3

end Cylinder.BMMTheorem

end
