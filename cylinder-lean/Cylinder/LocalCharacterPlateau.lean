module

public import Cylinder.ComponentCharacterNumeric
public import Cylinder.NumericalIdealFormula

/-! The exact numerical plateau calculations used before residual local
interpolation, including beta bounds and all three relation dimensions. -/

@[expose] public section
open scoped Classical BigOperators

namespace Cylinder.LocalCharacterPlateau

open Finset Cylinder.ComponentCharacterNumeric Cylinder.NumericalIdealFormula

theorem interval_bounds (b : ℕ → ℕ) (e : ℕ)
    (hb : ∀ i, i + 1 < e → b i ≤ b (i + 1) ∧ b (i + 1) ≤ b i + 1)
    (k l : ℕ) (hkl : k ≤ l) (hle : l < e) : b k ≤ b l ∧ b l ≤ b k + (l - k) := by
  have haux : ∀ t, k + t < e → b k ≤ b (k + t) ∧ b (k + t) ≤ b k + t := by
    intro t
    induction t with
    | zero => intro ht; simp
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hstep := hb (k + t) (by omega)
      simpa only [Nat.add_succ] using
        And.intro (hprev.1.trans hstep.1) (by omega : b (k + t + 1) ≤ b k + (t + 1))
  simpa only [Nat.add_sub_cancel' hkl] using haux (l - k) (by omega)

theorem beta_bounds (n : ℕ → ℕ) (e d m : ℕ)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hanti : Antitone n) (hlower : ∀ i < e, d + 2 - i ≤ n i)
    (hconn : ∀ i, 0 < i → i < e → n (i - 1) ≤ n i + 1)
    (hplateau : increment n d (3 * m + 3) = m) :
    m ≤ increment n d (e - 1) ∧ increment n d (e - 1) ≤ e - 2 * m - 4 ∧
      n (e - 1) = (d + 3 - e) + increment n d (e - 1) ∧
      increment n d (e - 1) + 2 * m + 2 ≤ e - 2 := by
  obtain ⟨hexact, hb⟩ := increment_bounds n e d hd hanti hlower hconn
  have hh := interval_bounds (increment n d) e hb (3 * m + 3) (e - 1) (by omega) (by omega)
  rw [hplateau] at hh
  have hn := hexact (e - 1) (by omega)
  omega

private theorem baseline_sum (q e : ℕ) (hqe : q ≤ e) :
    (∑ i ∈ range e, (q - i)) = triangular q := by
  have hsum : (∑ i ∈ range e, (q - i)) = ∑ i ∈ range q, (q - i) := by
    symm
    apply Finset.sum_subset (range_mono hqe)
    intro i hi hiq
    have hqi : q ≤ i := by simpa only [mem_range, not_lt] using hiq
    exact Nat.sub_eq_zero_of_le hqi
  rw [hsum]
  have hh := triangular_split q q (le_refl q)
  simpa only [Nat.sub_self, triangular, zero_add] using hh.symm

theorem plateau_sum (b : ℕ → ℕ) (e m v : ℕ)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e)
    (hb : ∀ i, i + 1 < e → b i ≤ b (i + 1) ∧ b (i + 1) ≤ b i + 1)
    (hplateau : ∀ r < 4, b (3 * m + r) = m) (hv0 : 2 * m ≤ v) (hv1 : v ≤ 2 * m + 2) :
    (∑ i ∈ range e, (v + 1 + b i - i)) + (∑ i ∈ range (3 * m), (m - b i)) =
      triangular (v + m + 1) := by
  have hterm : ∀ i < e, (v + 1 + b i - i) +
      (if i < 3 * m then m - b i else 0) = v + m + 1 - i := by
    intro i hie
    by_cases hi : i < 3 * m
    · have hhead := interval_bounds b e hb i (3 * m) (by omega) (by omega)
      rw [show 3 * m = 3 * m + 0 by omega, hplateau 0 (by omega)] at hhead
      rw [if_pos hi]
      omega
    · rw [if_neg hi, add_zero]
      by_cases hi3 : i ≤ 3 * m + 3
      · have hip : i = 3 * m + (i - 3 * m) := by omega
        have hbi := hplateau (i - 3 * m) (by omega)
        rw [← hip] at hbi
        rw [hbi]
        omega
      · have htail := interval_bounds b e hb (3 * m + 3) i (by omega) hie
        rw [hplateau 3 (by omega)] at htail
        omega
  have hsum := Finset.sum_congr rfl (fun i hi => hterm i (mem_range.mp hi))
  rw [sum_add_distrib] at hsum
  have hc : (∑ i ∈ range e, if i < 3 * m then m - b i else 0) =
      ∑ i ∈ range (3 * m), (m - b i) := by
    have heq : (∑ i ∈ range e, if i < 3 * m then m - b i else 0) =
        ∑ i ∈ range (3 * m), if i < 3 * m then m - b i else 0 := by
      symm
      apply Finset.sum_subset (range_mono (by omega))
      intro i hie hik
      simp only [mem_range] at hik
      simp only [if_neg hik]
    rw [heq]
    apply sum_congr rfl
    intro i hi
    exact if_pos (mem_range.mp hi)
  rw [hc, baseline_sum _ e (by omega)] at hsum
  exact hsum

/-- These are the manuscript's three exact local relation-defect sums,
derived from the connected character and its four-entry plateau. -/
theorem local_defect_sums (n : ℕ → ℕ) (e d m : ℕ)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hanti : Antitone n) (hlower : ∀ i < e, d + 2 - i ≤ n i)
    (hconn : ∀ i, 0 < i → i < e → n (i - 1) ≤ n i + 1)
    (hplateau : ∀ r < 4, increment n d (3 * m + r) = m)
    (v : ℕ) (hv0 : 2 * m ≤ v) (hv1 : v ≤ 2 * m + 2) :
    (∑ i ∈ range e, ((n i - (d - v + 1)) - (i - (d - v + 1)))) +
      (∑ i ∈ range (3 * m), (m - increment n d i)) = triangular (v + m + 1) := by
  obtain ⟨hexact, hb⟩ := increment_bounds n e d hd hanti hlower hconn
  have hterm : ∀ i < e, ((n i - (d - v + 1)) - (i - (d - v + 1))) =
      v + 1 + increment n d i - i := by
    intro i hie
    have hi := hexact i hie
    omega
  have heq := Finset.sum_congr rfl (fun i hi => hterm i (mem_range.mp hi))
  rw [heq]
  exact plateau_sum (increment n d) e m v hm hsmall hb hplateau hv0 hv1

#print axioms beta_bounds
#print axioms plateau_sum
#print axioms local_defect_sums

end Cylinder.LocalCharacterPlateau

end
