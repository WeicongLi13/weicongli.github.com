module

public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Int.Basic

/-! The strict comparisons used to make component moment forms agree. -/

@[expose] public section

namespace Cylinder.GlobalMomentArithmetic

theorem component_agreement_obstruction (p δ e f a ε : ℤ)
    (hp : 11 ≤ p) (hδ : 3 ≤ δ) (he : δ + 1 ≤ e) (hf : δ + 1 ≤ f)
    (ha : a ≤ 2) (hlow : e * (f - a) ≤ ε)
    (hhigh : 4 * ε ≤ δ * δ - p + 2) : False := by
  have hδ0 : 0 ≤ δ - 1 := by omega
  have he0 : 0 ≤ e := by omega
  have hfa : δ - 1 ≤ f - a := by omega
  have hprod : (δ + 1) * (δ - 1) ≤ e * (f - a) :=
    mul_le_mul he hfa hδ0 he0
  have hsq : 0 ≤ δ * δ := mul_self_nonneg δ
  nlinarith

theorem component_support_exceeds_intersection_bound (p s e a : ℤ)
    (he : 4 ≤ e) (hes : e ≤ s) (hps : s + 3 ≤ p - s) (ha : a ≤ 2) :
    e * (e - 1) < e * (p - s - a) := by
  have hdiff : e - 1 < p - s - a := by omega
  exact mul_lt_mul_of_pos_left hdiff (by omega)

theorem intersection_relation_degrees (p s : ℕ)
    (hp : 11 ≤ p) (hs : s ≤ (p - 3) / 2) :
    s - 2 ≤ p - 5 ∧ s - 2 ≤ p - 4 := by
  omega

end Cylinder.GlobalMomentArithmetic

end
