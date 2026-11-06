module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

/-! The staircase count in the many-two-point-rays lemma. Each condition
b(3j) ≥ j contributes one layer on every subsequent index below e. -/

@[expose] public section
open scoped BigOperators Classical
namespace Cylinder.ManyTwoStaircase
open Finset

theorem monotone_on_prefix (b : ℕ → ℕ) (e : ℕ)
    (hinc : ∀ j, j + 1 < e → b j ≤ b (j + 1)) :
    ∀ i j, i ≤ j → j < e → b i ≤ b j := by
  intro i j hij hj
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact (ih (by omega)).trans (hinc j hj)

theorem sum_layers (e k : ℕ) :
    (∑ j ∈ range e, if k ≤ j then (1 : ℕ) else 0) = e - k := by
  rw [Finset.sum_boole]
  have heq : (range e).filter (fun j => k ≤ j) = Ico k e := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [heq, Nat.card_Ico]
  simp only [Nat.cast_id]

theorem staircase_sum_lower (b : ℕ → ℕ) (e m : ℕ)
    (hinc : ∀ j, j + 1 < e → b j ≤ b (j + 1))
    (hstair : ∀ j, 1 ≤ j → j ≤ m → j ≤ b (3 * j)) :
    (∑ j ∈ range m, (e - 3 * (j + 1))) ≤ ∑ i ∈ range e, b i := by
  have hmono := monotone_on_prefix b e hinc
  have hpoint : ∀ i ∈ range e,
      (∑ j ∈ range m, if 3 * (j + 1) ≤ i then (1 : ℕ) else 0) ≤ b i := by
    intro i hi
    rw [Finset.sum_boole]
    have hsub : (range m).filter (fun j => 3 * (j + 1) ≤ i) ⊆ range (b i) := by
      intro j hj
      have hjs := mem_filter.mp hj
      have hst := hstair (j + 1) (by omega) (by have := mem_range.mp hjs.1; omega)
      have hbj := hmono (3 * (j + 1)) i hjs.2 (mem_range.mp hi)
      exact mem_range.mpr (by omega)
    simpa only [card_range, Nat.cast_id] using card_le_card hsub
  calc
    _ = ∑ j ∈ range m, ∑ i ∈ range e, if 3 * (j + 1) ≤ i then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro j _
      exact (sum_layers e (3 * (j + 1))).symm
    _ = ∑ i ∈ range e, ∑ j ∈ range m, if 3 * (j + 1) ≤ i then (1 : ℕ) else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum hpoint

private theorem twice_sum_successors (m : ℕ) :
    2 * (∑ j ∈ range m, (j + 1)) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ]; nlinarith

theorem staircase_bound (b : ℕ → ℕ) (e m : ℕ) (h3m : 3 * m ≤ e)
    (hinc : ∀ j, j + 1 < e → b j ≤ b (j + 1))
    (hstair : ∀ j, 1 ≤ j → j ≤ m → j ≤ b (3 * j)) :
    2 * m * e ≤ 2 * (∑ i ∈ range e, b i) + 3 * m * (m + 1) := by
  have hlo := staircase_sum_lower b e m hinc hstair
  have hterms : ∀ j ∈ range m, (e - 3 * (j + 1)) + 3 * (j + 1) = e := by
    intro j hj
    have hje := mem_range.mp hj
    apply Nat.sub_add_cancel
    omega
  have hsum := sum_congr rfl hterms
  rw [sum_add_distrib, ← mul_sum] at hsum
  simp only [sum_const, card_range, Nat.nsmul_eq_mul] at hsum
  have htwice := twice_sum_successors m
  nlinarith

end Cylinder.ManyTwoStaircase
end
