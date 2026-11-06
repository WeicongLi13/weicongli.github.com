module

public import Cylinder.NumericCharacterSequence

/-! The counting identity behind the ideal-dimension formula. -/

@[expose] public section

namespace Cylinder.NumericalIdealFormula

open Finset Cylinder.NumericCharacterSequence

def triangular : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangular n + n + 1

theorem triangular_split (N s : ℕ) (hs : s ≤ N) :
    triangular N = triangular (N - s) + ∑ i ∈ range s, (N - i) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hNs : s ≤ N := by omega
      have h := ih hNs
      have heq : N - s = (N - (s + 1)) + 1 := by omega
      rw [heq, triangular] at h
      rw [sum_range_succ]
      omega

variable {a : ℕ → ℕ} {s N : ℕ}

theorem initial_degree_interval (_h : Shape a s N) (d i : ℕ) :
    (range (d + 1)).filter (fun v => i ≤ v ∧ v < character a N i) =
      Ico i (min (character a N i) (d + 1)) := by
  ext v
  simp only [mem_filter, mem_range, mem_Ico]
  omega

theorem cumulative_formula (h : Shape a s N) (d : ℕ) :
    ∑ v ∈ range (d + 1), a v =
      ∑ i ∈ range s, (min (character a N i) (d + 1) - i) := by
  calc
    ∑ v ∈ range (d + 1), a v =
        ∑ v ∈ range (d + 1), ∑ i ∈ range s,
          if i ≤ v ∧ v < character a N i then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      rw [value_count h v, card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ range s, ∑ v ∈ range (d + 1),
          if i ≤ v ∧ v < character a N i then 1 else 0 := sum_comm
    _ = ∑ i ∈ range s, (min (character a N i) (d + 1) - i) := by
      apply sum_congr rfl
      intro i _
      rw [← sum_filter, ← card_eq_sum_ones, initial_degree_interval h d i]
      simp

theorem row_split (n i M : ℕ) (hi : i ≤ n) (hiM : i ≤ M) :
    M - i = (min n M - i) + (M - n) := by
  by_cases hn : n ≤ M
  · rw [min_eq_left hn]
    omega
  · rw [min_eq_right (by omega)]
    omega

theorem graded_dimension_identity (H : ℕ → ℕ) (hH : Monotone H)
    (h : Shape (firstDifference H) s N) (d : ℕ) (hs : s ≤ d + 1) :
    triangular (d + 1) = H d +
      (triangular (d + 1 - s) +
        ∑ i ∈ range s, (d + 1 - character (firstDifference H) N i)) := by
  have hc := cumulative_formula h d
  rw [sum_firstDifference H hH d] at hc
  have hrows : (∑ i ∈ range s, (d + 1 - i)) =
      (∑ i ∈ range s, (min (character (firstDifference H) N i) (d + 1) - i)) +
        ∑ i ∈ range s, (d + 1 - character (firstDifference H) N i) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have his := mem_range.mp hi
    have hin := character_ge_initial_size h (mem_range.mp hi)
    exact row_split _ _ _ (by omega) (by omega)
  rw [← hc] at hrows
  have ht := triangular_split (d + 1) s hs
  omega

end Cylinder.NumericalIdealFormula
