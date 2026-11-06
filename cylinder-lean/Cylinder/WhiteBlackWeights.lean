module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega

/-!
# Separating white and black intersection weights

These are the finite-sum identities used in Lemma `lem:balance`.
The geometric incidence sums are separate inputs here. They must be
proved for the actual plane intersections before applying these lemmas
to the cylinder problem.
-/

@[expose] public section

noncomputable section

namespace Cylinder.WhiteBlackWeights

open scoped BigOperators Classical

variable {ι : Type*}

def white (s : Finset ι) (r : ι → ℕ) : Finset ι := s.filter (fun i => r i = 0)
def black (s : Finset ι) (r : ι → ℕ) : Finset ι := s.filter (fun i => 2 ≤ r i)
def weight (r : ι → ℕ) (i : ι) : ℕ := r i - 1

theorem weight_eq_zero_of_not_black (r : ι → ℕ) (i : ι) (hi : ¬ 2 ≤ r i) :
    weight r i = 0 := by unfold weight; omega

theorem weight_pos_of_mem_black {s : Finset ι} {r : ι → ℕ} {i : ι}
    (hi : i ∈ black s r) : 0 < weight r i := by
  have h := (Finset.mem_filter.mp hi).2
  unfold weight
  omega

theorem sum_black_weight (s : Finset ι) (r : ι → ℕ) :
    (∑ i ∈ black s r, weight r i) = ∑ i ∈ s, weight r i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply weight_eq_zero_of_not_black
  intro h
  exact hnot (Finset.mem_filter.mpr ⟨hi, h⟩)

theorem count_identity (s : Finset ι) (r : ι → ℕ) :
    (∑ i ∈ s, r i) + (white s r).card = s.card + ∑ i ∈ black s r, weight r i := by
  rw [sum_black_weight]
  have hpoint (i : ι) : r i + (if r i = 0 then 1 else 0) = 1 + weight r i := by
    unfold weight
    split_ifs <;> omega
  have h := Finset.sum_congr rfl (fun i (_ : i ∈ s) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat, Finset.sum_boole,
    Nat.cast_id, mul_one] at h
  exact h

theorem sum_black_weight_eq_white_sub_one (s : Finset ι) (r : ι → ℕ)
    (htotal : (∑ i ∈ s, r i) + 1 = s.card) :
    (∑ i ∈ black s r, weight r i) = (white s r).card - 1 := by
  have h := count_identity s r
  omega

theorem white_card_eq_sum_black_weight_add_one (s : Finset ι) (r : ι → ℕ)
    (htotal : (∑ i ∈ s, r i) + 1 = s.card) :
    (white s r).card = (∑ i ∈ black s r, weight r i) + 1 := by
  have h := count_identity s r
  omega

theorem energy_identity (s : Finset ι) (r : ι → ℕ) :
    (∑ i ∈ black s r, weight r i * (weight r i + 1)) =
      ∑ i ∈ s, r i * (r i - 1) := by
  calc
    (∑ i ∈ black s r, weight r i * (weight r i + 1)) =
        ∑ i ∈ s, weight r i * (weight r i + 1) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      have hz : weight r i = 0 := weight_eq_zero_of_not_black r i (by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hi, h⟩))
      rw [hz, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz : r i = 0
      · simp [weight, hz]
      · have hr : r i - 1 + 1 = r i := by omega
        simp only [weight, hr, mul_comm]

theorem energy_ge_twice_weight (s : Finset ι) (r : ι → ℕ) :
    2 * (∑ i ∈ black s r, weight r i) ≤
      ∑ i ∈ black s r, weight r i * (weight r i + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hpos := weight_pos_of_mem_black hi
  nlinarith

theorem white_card_upper_bound (s : Finset ι) (r : ι → ℕ) (p : ℕ)
    (htotal : (∑ i ∈ s, r i) + 1 = s.card)
    (henergy : (∑ i ∈ s, r i * (r i - 1)) = p * (p - 1)) :
    (white s r).card ≤ 1 + p * (p - 1) / 2 := by
  have h := energy_ge_twice_weight s r
  rw [energy_identity, henergy] at h
  have hdiv : (∑ i ∈ black s r, weight r i) ≤ p * (p - 1) / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
    simpa only [mul_comm] using h
  rw [white_card_eq_sum_black_weight_add_one s r htotal]
  omega

theorem black_nonempty (s : Finset ι) (r : ι → ℕ) (p : ℕ) (hp : 2 ≤ p)
    (henergy : (∑ i ∈ s, r i * (r i - 1)) = p * (p - 1)) :
    (black s r).Nonempty := by
  by_contra hn
  have hempty : black s r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have h := energy_identity s r
  rw [hempty, Finset.sum_empty, henergy] at h
  have hpos : 0 < p * (p - 1) := Nat.mul_pos (by omega) (by omega)
  omega

end Cylinder.WhiteBlackWeights

end
