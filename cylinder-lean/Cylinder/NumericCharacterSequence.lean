module

public import Cylinder.IncidenceRestricted
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public meta import Lean.Elab.Tactic.Omega

/-! The finite numerical reconstruction used in the numerical-character lemma.
The hypotheses describe the Hilbert function of a binary Artin quotient.
This module does not assume any formula for the numerical character. -/

@[expose] public section

namespace Cylinder.NumericCharacterSequence

open Finset

/-- Initial growth, the first drop, monotonicity thereafter, and eventual vanishing. -/
structure Shape (a : ℕ → ℕ) (s N : ℕ) : Prop where
  positive : 0 < s
  initial : ∀ v < s, a v = v + 1
  first_drop : a s ≤ s
  decreasing : ∀ v, s ≤ v → a (v + 1) ≤ a v
  vanishing : ∀ v, N ≤ v → a v = 0

variable {a : ℕ → ℕ} {s N : ℕ}

def firstDifference (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => H 0
  | v + 1 => H (v + 1) - H v

theorem sum_firstDifference (H : ℕ → ℕ) (hH : Monotone H) (v : ℕ) :
    ∑ w ∈ range (v + 1), firstDifference H w = H v := by
  induction v with
  | zero => simp [firstDifference]
  | succ v ih =>
      rw [sum_range_succ, ih]
      simp only [firstDifference]
      have := hH (Nat.le_succ v)
      change H v ≤ H (v + 1) at this
      omega

def degreesAbove (a : ℕ → ℕ) (N i : ℕ) : Finset ℕ :=
  (range N).filter (fun v => i < a v)

/-- One more than the last degree whose value exceeds the index. -/
def character (a : ℕ → ℕ) (N i : ℕ) : ℕ :=
  (degreesAbove a N i).sup Nat.succ

theorem decreasing_on_tail (h : Shape a s N) {v w : ℕ} (hv : s ≤ v) (hvw : v ≤ w) :
    a w ≤ a v :=
  antitoneOn_nat_Ici_of_succ_le h.decreasing hv (le_trans hv hvw) hvw

theorem value_le_initial_degree (h : Shape a s N) (v : ℕ) : a v ≤ v + 1 := by
  by_cases hv : v < s
  · rw [h.initial v hv]
  · have hav := decreasing_on_tail h (v := s) (w := v) (le_refl s) (by omega)
    have := h.first_drop
    omega

theorem value_le_initial_size (h : Shape a s N) (v : ℕ) : a v ≤ s := by
  by_cases hv : v < s
  · rw [h.initial v hv]
    omega
  · exact le_trans (decreasing_on_tail h (le_refl s) (by omega)) h.first_drop

theorem character_le_bound (i : ℕ) : character a N i ≤ N := by
  apply Finset.sup_le
  intro v hv
  have := (Finset.mem_filter.mp hv).1
  simp only [Finset.mem_range] at this
  omega

theorem character_ge_initial_size (h : Shape a s N) {i : ℕ} (hi : i < s) :
    s ≤ character a N i := by
  have hv : s - 1 < s := by omega
  have has : a (s - 1) = s := by
    rw [h.initial (s - 1) hv]
    omega
  have hN : s - 1 < N := by
    by_contra hn
    have := h.vanishing (s - 1) (by omega)
    omega
  have hmem : s - 1 ∈ degreesAbove a N i := by simp [degreesAbove, hN, has, hi]
  have := Finset.le_sup (f := Nat.succ) hmem
  change s ≤ character a N i
  simpa [character, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ s)] using this

theorem character_antitone : Antitone (character a N) := by
  intro i j hij
  apply Finset.sup_le
  intro v hv
  have hm := Finset.mem_filter.mp hv
  have hmem : v ∈ degreesAbove a N i :=
    Finset.mem_filter.mpr ⟨hm.1, lt_of_le_of_lt hij hm.2⟩
  exact Finset.le_sup hmem

theorem interval_iff_value (h : Shape a s N) {i v : ℕ} (_hi : i < s) :
    i ≤ v ∧ v < character a N i ↔ i < a v := by
  constructor
  · rintro ⟨hiv, hv⟩
    obtain ⟨w, hw, hvw⟩ := Finset.lt_sup_iff.mp hv
    have hw' := (Finset.mem_filter.mp hw).2
    have hvw' : v ≤ w := by omega
    by_cases hvs : v < s
    · rw [h.initial v hvs]
      omega
    · exact lt_of_lt_of_le hw' (decreasing_on_tail h (by omega) hvw')
  · intro hiv
    have hvN : v < N := by
      by_contra hvN
      have := h.vanishing v (by omega)
      omega
    have hmem : v ∈ degreesAbove a N i := by simp [degreesAbove, hvN, hiv]
    have hsup := Finset.le_sup (f := Nat.succ) hmem
    have hav := value_le_initial_degree h v
    exact ⟨by omega, by change v < (degreesAbove a N i).sup Nat.succ; omega⟩

theorem value_count (h : Shape a s N) (v : ℕ) :
    a v = ((range s).filter (fun i => i ≤ v ∧ v < character a N i)).card := by
  have heq : (range s).filter (fun i => i ≤ v ∧ v < character a N i) = range (a v) := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hi, hv⟩
      exact (interval_iff_value h hi).mp hv
    · intro hi
      have his : i < s := lt_of_lt_of_le hi (value_le_initial_size h v)
      exact ⟨his, (interval_iff_value h his).mpr hi⟩
  rw [heq, card_range]

theorem degree_interval (_h : Shape a s N) {i : ℕ} (_hi : i < s) :
    (range N).filter (fun v => i ≤ v ∧ v < character a N i) = Ico i (character a N i) := by
  ext v
  simp only [mem_filter, mem_range, mem_Ico]
  have hb := character_le_bound (a := a) (N := N) i
  omega

theorem length_formula (h : Shape a s N) :
    ∑ v ∈ range N, a v = ∑ i ∈ range s, (character a N i - i) := by
  calc
    ∑ v ∈ range N, a v =
        ∑ v ∈ range N, ∑ i ∈ range s, if i ≤ v ∧ v < character a N i then 1 else 0 := by
      apply sum_congr rfl
      intro v _
      rw [value_count h v, card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ range s, ∑ v ∈ range N, if i ≤ v ∧ v < character a N i then 1 else 0 :=
      sum_comm
    _ = ∑ i ∈ range s, (character a N i - i) := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter, ← card_eq_sum_ones, degree_interval h (mem_range.mp hi)]
      simp

theorem tail_degree_interval (_h : Shape a s N) (v : ℕ) {i : ℕ} (_hi : i < s) :
    (Ico (v + 1) N).filter (fun w => i ≤ w ∧ w < character a N i) =
      Ico (max i (v + 1)) (character a N i) := by
  ext w
  simp only [mem_filter, mem_Ico]
  have hb := character_le_bound (a := a) (N := N) i
  omega

/-- The sum of first differences above a degree, expressed by the character. -/
theorem tail_defect_formula (h : Shape a s N) (v : ℕ) :
    ∑ w ∈ Ico (v + 1) N, a w =
      ∑ i ∈ range s, ((character a N i - (v + 1)) - (i - (v + 1))) := by
  calc
    ∑ w ∈ Ico (v + 1) N, a w =
        ∑ w ∈ Ico (v + 1) N, ∑ i ∈ range s,
          if i ≤ w ∧ w < character a N i then 1 else 0 := by
      apply sum_congr rfl
      intro w _
      rw [value_count h w, card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ range s, ∑ w ∈ Ico (v + 1) N,
          if i ≤ w ∧ w < character a N i then 1 else 0 := sum_comm
    _ = ∑ i ∈ range s, ((character a N i - (v + 1)) - (i - (v + 1))) := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter, ← card_eq_sum_ones, tail_degree_interval h v (mem_range.mp hi)]
      simp only [Nat.card_Ico]
      have hn := character_ge_initial_size h (mem_range.mp hi)
      omega

theorem tail_positive_iff (h : Shape a s N) (v : ℕ) :
    0 < ∑ w ∈ Ico (v + 1) N, a w ↔ v + 1 < character a N 0 := by
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨w, hw, haw⟩
    have hwi := Finset.mem_Ico.mp hw
    have hinterval := (interval_iff_value h h.positive).mpr haw
    omega
  · intro hv
    have hn := character_le_bound (a := a) (N := N) 0
    refine ⟨v + 1, by simp only [mem_Ico]; omega, ?_⟩
    exact (interval_iff_value h h.positive).mp ⟨by omega, hv⟩

theorem length_of_firstDifference (H : ℕ → ℕ) (hH : Monotone H)
    (h : Shape (firstDifference H) s N) :
    H (N - 1) = ∑ i ∈ range s, (character (firstDifference H) N i - i) := by
  have hN : 0 < N := lt_of_lt_of_le h.positive
    (le_trans (character_ge_initial_size h h.positive) (character_le_bound 0))
  have hs := sum_firstDifference H hH (N - 1)
  have heq : N - 1 + 1 = N := by omega
  rw [heq] at hs
  rw [← hs]
  exact length_formula h

theorem tail_of_firstDifference (H : ℕ → ℕ) (hH : Monotone H) {N L : ℕ}
    (hN : 0 < N) (hstable : ∀ w, N - 1 ≤ w → H w = L) (v : ℕ) :
    ∑ w ∈ Ico (v + 1) N, firstDifference H w = L - H v := by
  by_cases hv : v + 1 ≤ N
  · have hs := Finset.sum_range_add_sum_Ico (firstDifference H) hv
    rw [sum_firstDifference H hH v] at hs
    have hm := sum_firstDifference H hH (N - 1)
    have heq : N - 1 + 1 = N := by omega
    rw [heq, hstable (N - 1) (le_refl _)] at hm
    rw [hm] at hs
    omega
  · have hstablev := hstable v (by omega)
    rw [Finset.Ico_eq_empty_of_le (by omega : N ≤ v + 1), sum_empty, hstablev,
      Nat.sub_self]

/-- The numerical defect formula, before its interpretation as sheaf cohomology. -/
theorem defect_of_firstDifference (H : ℕ → ℕ) (hH : Monotone H)
    (h : Shape (firstDifference H) s N) (L : ℕ)
    (hstable : ∀ w, N - 1 ≤ w → H w = L) (v : ℕ) :
    L - H v = ∑ i ∈ range s,
      ((character (firstDifference H) N i - (v + 1)) - (i - (v + 1))) := by
  have hN : 0 < N := lt_of_lt_of_le h.positive
    (le_trans (character_ge_initial_size h h.positive) (character_le_bound 0))
  rw [← tail_of_firstDifference H hH hN hstable v]
  exact tail_defect_formula h v

end Cylinder.NumericCharacterSequence
