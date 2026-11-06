module

public import Cylinder.NumericCharacterSequence
public import Mathlib.Tactic.Linarith

/-! Numerical character bounds from the actual first entry and the lower
bound at every actual gap. Connectedness is not assumed. -/

@[expose] public section

namespace Cylinder.CharacterBounds

open Finset Cylinder.NumericCharacterSequence

theorem slope_lower_of_gap_bounds (n : ℕ → ℕ) (s d : ℕ)
    (h0 : d + 2 ≤ n 0)
    (hgap : ∀ j, 0 < j → j < s → n j + 2 ≤ n (j - 1) → d + 2 ≤ n j) :
    ∀ i, i < s → d + 2 ≤ n i + i := by
  intro i
  induction i with
  | zero => intro hi; simpa using h0
  | succ i ih =>
    intro hi
    have hiprev : i < s := by omega
    have hprev := ih hiprev
    by_cases hgi : n (i + 1) + 2 ≤ n i
    · have hn := hgap (i + 1) (by omega) hi (by simpa using hgi)
      omega
    · omega

private theorem twice_sum_range_id (t : ℕ) :
    2 * (∑ i ∈ range t, i) + t = t * t := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ]; nlinarith

theorem prefix_bound (n : ℕ → ℕ) (t d : ℕ)
    (hn : ∀ i < t, i ≤ n i) (hslope : ∀ i < t, d + 2 ≤ n i + i) :
    t * (d + 3 - t) ≤ ∑ i ∈ range t, (n i - i) := by
  have hsum : t * (d + 2) ≤ (∑ i ∈ range t, (n i - i)) +
      2 * (∑ i ∈ range t, i) := by
    have h := Finset.sum_le_sum (s := range t) (f := fun _ => d + 2)
      (g := fun i => (n i - i) + 2 * i) (by
        intro i hi
        have hn' := hn i (mem_range.mp hi)
        have hs' := hslope i (mem_range.mp hi)
        omega)
    calc
      _ = ∑ i ∈ range t, (d + 2) := by simp only [sum_const, card_range, Nat.nsmul_eq_mul]
      _ ≤ ∑ i ∈ range t, ((n i - i) + 2 * i) := h
      _ = _ := by rw [sum_add_distrib, ← mul_sum]
  have hid := twice_sum_range_id t
  by_cases ht : t ≤ d + 3
  · have hsub : d + 3 - t + t = d + 3 := by omega
    nlinarith
  · have hz : d + 3 - t = 0 := by omega
    simp [hz]

theorem max_sum_bound (s d : ℕ) :
    s * (d + 3 - s) ≤ ∑ i ∈ range s, (max s (d + 2 - i) - i) := by
  apply prefix_bound
  · intro i hi
    exact (by omega : i ≤ s).trans (le_max_left _ _)
  · intro i hi
    have hmax := le_max_right s (d + 2 - i)
    omega

variable {a : ℕ → ℕ} {s N d : ℕ}

theorem character_lower (h : Shape a s N) (h0 : d + 2 ≤ character a N 0)
    (hgap : ∀ j, 0 < j → j < s →
      character a N j + 2 ≤ character a N (j - 1) → d + 2 ≤ character a N j)
    (i : ℕ) (hi : i < s) :
    max s (d + 2 - i) ≤ character a N i := by
  apply max_le
  · exact character_ge_initial_size h hi
  · have hslope := slope_lower_of_gap_bounds (character a N) s d h0 hgap i hi
    omega

theorem character_sum_bound (h : Shape a s N) (h0 : d + 2 ≤ character a N 0)
    (hgap : ∀ j, 0 < j → j < s →
      character a N j + 2 ≤ character a N (j - 1) → d + 2 ≤ character a N j) :
    (∑ i ∈ range s, (max s (d + 2 - i) - i)) ≤
      ∑ i ∈ range s, (character a N i - i) := by
  apply sum_le_sum
  intro i hi
  exact Nat.sub_le_sub_right (character_lower h h0 hgap i (mem_range.mp hi)) i

theorem truncated_character_bound (h : Shape a s N) (h0 : d + 2 ≤ character a N 0)
    (hgap : ∀ j, 0 < j → j < s →
      character a N j + 2 ≤ character a N (j - 1) → d + 2 ≤ character a N j)
    (t : ℕ) (ht : t ≤ s) :
    t * (d + 3 - t) ≤ ∑ i ∈ range s, (character a N i - i) := by
  apply (prefix_bound (character a N) t d ?_ ?_).trans
    (sum_le_sum_of_subset (range_mono ht))
  · intro i hi
    have his : i < s := by omega
    exact (by omega : i ≤ s).trans (character_ge_initial_size h his)
  · intro i hi
    exact slope_lower_of_gap_bounds (character a N) s d h0 hgap i (by omega)

#print axioms character_lower
#print axioms character_sum_bound
#print axioms max_sum_bound
#print axioms truncated_character_bound

end Cylinder.CharacterBounds

end
