module

public import Cylinder.EvaluationProjection
public import Cylinder.Recurrence
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.Ring

/-! The actual moment formulas and recurrence on a two-point ray. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Cylinder.TwoRayMoments

variable {K : Type*} [Field K]

def twoMoment (t c : Fin 2 → K) (j : ℕ) : K := ∑ i : Fin 2, c i * t i ^ j

def normalizedMoment (t c : Fin 2 → K) (n : ℕ) : K := twoMoment t c (n + 1) / twoMoment t c 1

theorem coefficients_opposite (t c : Fin 2 → K) (hzero : twoMoment t c 0 = 0) :
    c 1 = -c 0 := by
  have h : c 0 + c 1 = 0 := by simpa [twoMoment, Fin.sum_univ_succ] using hzero
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)

theorem moment_difference (t c : Fin 2 → K) (hzero : twoMoment t c 0 = 0) (j : ℕ) :
    twoMoment t c j = c 0 * (t 0 ^ j - t 1 ^ j) := by
  have hc := coefficients_opposite t c hzero
  simp only [twoMoment, Fin.sum_univ_two, hc]
  ring

theorem first_moment_ne_zero (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) : twoMoment t c 1 ≠ 0 := by
  rw [moment_difference t c hzero, pow_one, pow_one]
  exact mul_ne_zero hc (sub_ne_zero.mpr (ht.ne (by decide : (0 : Fin 2) ≠ 1)))

theorem normalized_difference (t c : Fin 2 → K) (_ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) (n : ℕ) :
    normalizedMoment t c n = (t 0 ^ (n + 1) - t 1 ^ (n + 1)) / (t 0 - t 1) := by
  unfold normalizedMoment
  rw [moment_difference t c hzero, moment_difference t c hzero, pow_one, pow_one]
  exact mul_div_mul_left _ _ hc

theorem normalized_zero (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) : normalizedMoment t c 0 = 1 := by
  unfold normalizedMoment
  simp only [zero_add, div_self (first_moment_ne_zero t c ht hc hzero)]

theorem normalized_one (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) : normalizedMoment t c 1 = t 0 + t 1 := by
  rw [normalized_difference t c ht hc hzero]
  have hd : t 0 - t 1 ≠ 0 := sub_ne_zero.mpr (ht.ne (by decide : (0 : Fin 2) ≠ 1))
  apply (div_eq_iff hd).mpr
  ring

theorem normalized_step (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) (n : ℕ) :
    normalizedMoment t c (n + 2) = (t 0 + t 1) * normalizedMoment t c (n + 1) -
      (t 0 * t 1) * normalizedMoment t c n := by
  rw [normalized_difference t c ht hc hzero, normalized_difference t c ht hc hzero,
    normalized_difference t c ht hc hzero]
  have hd : t 0 - t 1 ≠ 0 := sub_ne_zero.mpr (ht.ne (by decide : (0 : Fin 2) ≠ 1))
  field_simp
  simp only [pow_succ]
  ring

theorem normalized_eq_recurrence (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) :
    ∀ n, normalizedMoment t c n = Recurrence.moment (t 0 + t 1) (t 0 * t 1) n :=
  Recurrence.moment_unique _ _ _ (normalized_zero t c ht hc hzero)
    (normalized_one t c ht hc hzero) (normalized_step t c ht hc hzero)

theorem normalized_two (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) :
    normalizedMoment t c 2 = t 0 ^ 2 + t 0 * t 1 + t 1 ^ 2 := by
  rw [normalized_eq_recurrence t c ht hc hzero, Recurrence.moment_two]
  ring

theorem normalized_sum (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) (n : ℕ) :
    normalizedMoment t c n = ∑ j ∈ Finset.range (n + 1), t 0 ^ (n - j) * t 1 ^ j := by
  have hne : t 0 ≠ t 1 := ht.ne (by decide : (0 : Fin 2) ≠ 1)
  have hgeom := (Commute.all (t 1) (t 0)).geom_sum₂ hne.symm (n + 1)
  have hsum : (∑ j ∈ Finset.range (n + 1), t 0 ^ (n - j) * t 1 ^ j) =
      (t 1 ^ (n + 1) - t 0 ^ (n + 1)) / (t 1 - t 0) := by
    simpa only [Nat.add_sub_cancel, mul_comm] using hgeom
  rw [hsum, normalized_difference t c ht hc hzero]
  field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr hne.symm]
  ring

end Cylinder.TwoRayMoments

end
