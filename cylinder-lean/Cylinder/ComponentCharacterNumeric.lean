module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-! The numerical increments and small relation dimensions of a connected character. -/

@[expose] public section
open scoped BigOperators

namespace Cylinder.ComponentCharacterNumeric

def increment (n : ℕ → ℕ) (d j : ℕ) : ℕ := n j - (d + 2 - j)

theorem increment_bounds (n : ℕ → ℕ) (e d : ℕ) (hd : 2 * e ≤ d)
    (hanti : Antitone n) (hlower : ∀ j < e, d + 2 - j ≤ n j)
    (hconn : ∀ j, 0 < j → j < e → n (j - 1) ≤ n j + 1) :
    (∀ j < e, n j = (d + 2 - j) + increment n d j) ∧
    ∀ j, j + 1 < e → increment n d j ≤ increment n d (j + 1) ∧
      increment n d (j + 1) ≤ increment n d j + 1 := by
  constructor
  · intro j hj
    have h := hlower j hj
    unfold increment
    omega
  · intro j hj
    have h0 := hlower j (by omega)
    have h1 := hlower (j + 1) hj
    have ha := hanti (Nat.le_succ j)
    have hc := hconn (j + 1) (by omega) hj
    change n (j + 1) ≤ n j at ha
    change n j ≤ n (j + 1) + 1 at hc
    unfold increment
    omega

private theorem twice_sum_indices (e : ℕ) :
    2 * (∑ j ∈ Finset.range e, j) + e = e * e := by
  induction e with
  | zero => simp
  | succ e ih => rw [Finset.sum_range_succ]; nlinarith

theorem length_increment_sum (n : ℕ → ℕ) (e d N : ℕ) (hd : 2 * e ≤ d)
    (hlower : ∀ j < e, d + 2 - j ≤ n j)
    (hlength : N = ∑ j ∈ Finset.range e, (n j - j)) :
    e * (d + 3 - e) + (∑ j ∈ Finset.range e, increment n d j) = N := by
  have hp : ∀ j ∈ Finset.range e, (n j - j) + 2 * j = d + 2 + increment n d j := by
    intro j hj
    have hje := Finset.mem_range.mp hj
    have hn := hlower j hje
    unfold increment
    omega
  have hsum := Finset.sum_congr rfl hp
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, Nat.nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  have hi := twice_sum_indices e
  have hsub : d + 3 - e + e = d + 3 := by omega
  have hproduct := congrArg (fun k : ℕ => e * k) hsub
  simp only [Nat.mul_add] at hproduct
  rw [← hlength] at hsum
  nlinarith

theorem zero_third_initial_entries (n : ℕ → ℕ) (e d : ℕ) (he : 4 ≤ e)
    (hd : 2 * e ≤ d) (hanti : Antitone n) (hlower : ∀ j < e, d + 2 - j ≤ n j)
    (hconn : ∀ j, 0 < j → j < e → n (j - 1) ≤ n j + 1)
    (hb3 : increment n d 3 = 0) :
    n 0 = d + 2 ∧ n 1 = d + 1 ∧ n 2 = d ∧ n 3 = d - 1 := by
  obtain ⟨hexact, hbounds⟩ := increment_bounds n e d hd hanti hlower hconn
  have h01 := (hbounds 0 (by omega)).1
  have h12 := (hbounds 1 (by omega)).1
  have h23 := (hbounds 2 (by omega)).1
  change increment n d 0 ≤ increment n d 1 at h01
  change increment n d 1 ≤ increment n d 2 at h12
  change increment n d 2 ≤ increment n d 3 at h23
  have h0 := hexact 0 (by omega)
  have h1 := hexact 1 (by omega)
  have h2 := hexact 2 (by omega)
  have h3 := hexact 3 (by omega)
  omega

theorem small_defect_sums (n : ℕ → ℕ) (e d : ℕ) (he : 4 ≤ e)
    (hd : 2 * e ≤ d) (hanti : Antitone n) (hlower : ∀ j < e, d + 2 - j ≤ n j)
    (hconn : ∀ j, 0 < j → j < e → n (j - 1) ≤ n j + 1)
    (hb3 : increment n d 3 = 0) :
    (∑ j ∈ Finset.range e, ((n j - d) - (j - d))) = 3 ∧
    (∑ j ∈ Finset.range e, ((n j - (d - 1)) - (j - (d - 1)))) = 6 := by
  obtain ⟨h0, h1, h2, h3⟩ := zero_third_initial_entries n e d he hd hanti hlower hconn hb3
  have htail : ∀ j ∈ Finset.range e, j ∉ Finset.range 3 →
      ((n j - d) - (j - d)) = 0 ∧
        ((n j - (d - 1)) - (j - (d - 1))) = 0 := by
    intro j hj hj3
    have hje := Finset.mem_range.mp hj
    have hj3' : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj3
    have hnj := hanti hj3'
    omega
  have hsum1 : (∑ j ∈ Finset.range e, ((n j - d) - (j - d))) =
      ∑ j ∈ Finset.range 3, ((n j - d) - (j - d)) := by
    symm
    exact Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hj3 => (htail j hj hj3).1)
  have hsum2 : (∑ j ∈ Finset.range e, ((n j - (d - 1)) - (j - (d - 1)))) =
      ∑ j ∈ Finset.range 3, ((n j - (d - 1)) - (j - (d - 1))) := by
    symm
    exact Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hj3 => (htail j hj hj3).2)
  rw [hsum1, hsum2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2]
  omega

end Cylinder.ComponentCharacterNumeric

end
