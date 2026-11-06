module

public import Cylinder.CharacterBounds

/-! The character bounds for 2n points with a full-support relation in
degree n-1 force initial degree at most two, including the small orders. -/

@[expose] public section
open scoped BigOperators

namespace Cylinder.ThreeNetConicArithmetic

theorem initial_degree_le_two (n s : ℕ)
    (hbound : (∑ i ∈ Finset.range s, (max s (n - 1 + 2 - i) - i)) ≤ 2 * n)
    (htruncated : ∀ t, t ≤ s → t * (n - 1 + 3 - t) ≤ 2 * n) : s ≤ 2 := by
  by_contra hlarge
  have hs : 3 ≤ s := by omega
  by_cases hn : 4 ≤ n
  · have h := htruncated 3 hs
    omega
  · have hprefix : (∑ i ∈ Finset.range 3, (max s (n - 1 + 2 - i) - i)) ≤ 2 * n := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hs)
        (fun _ _ _ => Nat.zero_le _)).trans hbound
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hprefix
    have h0 := Nat.le_max_left s (n - 1 + 2 - 0)
    have h1 := Nat.le_max_left s (n - 1 + 2 - 1)
    have h2 := Nat.le_max_left s (n - 1 + 2 - 2)
    by_cases hn3 : n = 3
    · have hfirst := Nat.le_max_right s (n - 1 + 2 - 0)
      omega
    · omega

end Cylinder.ThreeNetConicArithmetic
end
