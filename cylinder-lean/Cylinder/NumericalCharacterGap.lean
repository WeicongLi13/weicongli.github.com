module

public import Cylinder.NumericalIdealFormula

/-! Exact numerical consequences of a gap in the reconstructed character.
No plateau or length formula is added as a hypothesis. -/

@[expose] public section

namespace Cylinder.NumericalCharacterGap

open Finset Cylinder.NumericCharacterSequence Cylinder.NumericalIdealFormula

variable {a : ℕ → ℕ} {s N j : ℕ}

theorem gap_plateau (h : Shape a s N) (hj0 : 0 < j) (hjs : j < s)
    (hgap : character a N j + 2 ≤ character a N (j - 1)) :
    s ≤ character a N j ∧
      a (character a N j) = j ∧ a (character a N j + 1) = j := by
  have hqs := character_ge_initial_size h hjs
  have hjprev : j - 1 < s := by omega
  have hlower := (interval_iff_value h hjprev).mp
    (show j - 1 ≤ character a N j ∧ character a N j < character a N (j - 1) by omega)
  have hupper : a (character a N j) ≤ j := by
    by_contra hn
    have hbad := (interval_iff_value h hjs).mpr (by omega : j < a (character a N j))
    omega
  have hq : a (character a N j) = j := by omega
  have hlower' := (interval_iff_value h hjprev).mp
    (show j - 1 ≤ character a N j + 1 ∧
      character a N j + 1 < character a N (j - 1) by omega)
  have hupper' := h.decreasing (character a N j) hqs
  exact ⟨hqs, hq, by omega⟩

theorem character_head_above_gap (h : Shape a s N) (hj0 : 0 < j) (hjs : j < s)
    (hgap : character a N j + 2 ≤ character a N (j - 1)) {i : ℕ} (hi : i < j) :
    character a N j ≤ character a N i := by
  have hmono := character_antitone (a := a) (N := N) (show i ≤ j - 1 by omega)
  omega

theorem character_tail_below_gap {i : ℕ} (hi : j ≤ i) :
    character a N i ≤ character a N j := character_antitone hi

theorem gap_tail_sum (h : Shape a s N) (hj0 : 0 < j) (hjs : j < s)
    (hgap : character a N j + 2 ≤ character a N (j - 1)) :
    (∑ i ∈ range s, (character a N i - character a N j)) =
      ∑ i ∈ range j, (character a N i - character a N j) := by
  symm
  apply sum_subset (range_mono (by omega : j ≤ s))
  intro i his hij
  have hji : j ≤ i := by simp only [mem_range] at hij; omega
  exact Nat.sub_eq_zero_of_le (character_tail_below_gap hji)

/-- The tail defect at `q-1` has no residual index subtraction. -/
theorem gap_defect_sum (h : Shape a s N) (hjs : j < s) :
    (∑ i ∈ range s,
      ((character a N i - (character a N j - 1 + 1)) -
        (i - (character a N j - 1 + 1)))) =
      ∑ i ∈ range s, (character a N i - character a N j) := by
  have hqs := character_ge_initial_size h hjs
  have hq : character a N j - 1 + 1 = character a N j := by
    have := h.positive
    omega
  rw [hq]
  apply sum_congr rfl
  intro i hi
  have his := mem_range.mp hi
  have hiq : i - character a N j = 0 := by omega
  rw [hiq, Nat.sub_zero]

/-- The reconstructed head length is exactly the degree-j factor's
triangular contribution plus the actual remaining numerical defect. -/
theorem gap_head_length (h : Shape a s N) (hj0 : 0 < j) (hjs : j < s)
    (hgap : character a N j + 2 ≤ character a N (j - 1)) :
    triangular (character a N j) - triangular (character a N j - j) +
      (∑ i ∈ range s, (character a N i - character a N j)) =
        ∑ i ∈ range j, (character a N i - i) := by
  have hqs := character_ge_initial_size h hjs
  have hqj : j ≤ character a N j := by omega
  have htri := triangular_split (character a N j) j hqj
  have ht : triangular (character a N j) - triangular (character a N j - j) =
      ∑ i ∈ range j, (character a N j - i) := by omega
  rw [ht, gap_tail_sum h hj0 hjs hgap, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hij := mem_range.mp hi
  have hni := character_head_above_gap h hj0 hjs hgap hij
  have hiq : i ≤ character a N j := by omega
  omega

#print axioms gap_plateau
#print axioms gap_defect_sum
#print axioms gap_head_length

end Cylinder.NumericalCharacterGap

end
