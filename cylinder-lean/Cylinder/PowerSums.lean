module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Field.ZMod
public import Lean.Elab.Tactic.Omega

/-! Finite-field power sums used to extract the highest monomial of the
projection polynomial. These are field identities, not assumptions on a
projection or on the cylinder conjecture. -/

@[expose] public section

namespace Cylinder.PowerSums

open Finset

theorem sum_pow_nonzero (K : Type*) [Field K] [Fintype K]
    (i : ℕ) (hi : i ≠ 0) :
    (∑ x : K, x ^ i) = if Fintype.card K - 1 ∣ i then -1 else 0 := by
  classical
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hu : univ.map φ = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
      mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ x : K, x ^ i) = ∑ x ∈ univ \ {(0 : K)}, x ^ i := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton,
        zero_pow hi, add_zero]
    _ = ∑ x : Kˣ, (x ^ i : K) := by
      simp [φ, ← hu, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units K i

theorem sum_pow_card_sub_one (K : Type*) [Field K] [Fintype K] :
    (∑ x : K, x ^ (Fintype.card K - 1)) = -1 := by
  have hc : 1 < Fintype.card K := Fintype.one_lt_card
  rw [sum_pow_nonzero K _ (by omega), ite_eq_left (dvd_refl _)]

theorem prime_sum_pow_low (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p - 1) :
    (∑ x : ZMod p, x ^ i) = 0 := by
  simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by simpa using hi)

theorem prime_sum_pow_boundary (p : ℕ) [Fact p.Prime] :
    (∑ x : ZMod p, x ^ (p - 1)) = -1 := by
  simpa using sum_pow_card_sub_one (ZMod p)

end Cylinder.PowerSums
