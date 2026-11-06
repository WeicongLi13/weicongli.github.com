import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Rigidity of affine permutations in the linear column model of cyclic codes.
This file contains no classification or analytic input. -/

namespace NSDensity

/-- A linear map that sends every power of a spanning element to the
corresponding power of one other element necessarily preserves products. -/
theorem linearMap_mul_of_powers {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (T : E →ₗ[F] E)
    (hspan : Submodule.span F (Set.range fun k : ℕ => a ^ k) = ⊤)
    (hT : ∀ k : ℕ, T (a ^ k) = b ^ k) :
    ∀ x y : E, T (x * y) = T x * T y := by
  intro x y
  have hx : x ∈ Submodule.span F (Set.range fun k : ℕ => a ^ k) := by rw [hspan]; trivial
  have hy : y ∈ Submodule.span F (Set.range fun k : ℕ => a ^ k) := by rw [hspan]; trivial
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
      obtain ⟨k, rfl⟩ := hu
      obtain ⟨l, rfl⟩ := hv
      rw [← pow_add, hT, hT, hT, pow_add]
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u v w hu hv hw huw hvw => simp [add_mul, huw, hvw]
  | add_right u v w hu hv hw huv huw => simp [mul_add, huv, huw]
  | smul_left r u v hu hv huv => simp [huv]
  | smul_right r u v hu hv huv => simp [huv]

/-- Over finite fields, the above linear map is a power of the relative
Frobenius. This proves that an affine multiplier preserving the column
relations belongs to the usual standard group. -/
theorem linearEquiv_powers_eq_frobenius {F E : Type*} [Field F] [Fintype F]
    [Field E] [Finite E] [Algebra F E]
    (a b : E) (T : E ≃ₗ[F] E)
    (hspan : Submodule.span F (Set.range fun k : ℕ => a ^ k) = ⊤)
    (hT : ∀ k : ℕ, T (a ^ k) = b ^ k) :
    ∃ j : ℕ, ∀ x : E, T x = x ^ (Fintype.card F ^ j) := by
  have hone : T 1 = 1 := by simpa using hT 0
  let e : E ≃ₐ[F] E := AlgEquiv.ofLinearEquiv T hone
    (linearMap_mul_of_powers a b T.toLinearMap hspan hT)
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F E).2 e
  refine ⟨j.val, fun x => ?_⟩
  have hx := congrArg (fun f : E ≃ₐ[F] E => f x) hj
  simpa only [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    e, AlgEquiv.ofLinearEquiv_apply] using hx.symm

/-- Including a cyclic shift gives exactly multiplication by a nonzero
constant followed by a relative Frobenius power. -/
theorem linearEquiv_scaled_powers_eq_standard {F E : Type*} [Field F] [Fintype F]
    [Field E] [Finite E] [Algebra F E]
    (a b c : E) (hc : c ≠ 0) (T : E ≃ₗ[F] E)
    (hspan : Submodule.span F (Set.range fun k : ℕ => a ^ k) = ⊤)
    (hT : ∀ k : ℕ, T (a ^ k) = c * b ^ k) :
    ∃ j : ℕ, ∀ x : E, T x = c * x ^ (Fintype.card F ^ j) := by
  let S : E ≃ₗ[F] E := T.trans
    ((LinearEquiv.smulOfNeZero E E c⁻¹ (inv_ne_zero hc)).restrictScalars F)
  have hS : ∀ k : ℕ, S (a ^ k) = b ^ k := by
    intro k
    change c⁻¹ * T (a ^ k) = b ^ k
    rw [hT, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  obtain ⟨j, hj⟩ := linearEquiv_powers_eq_frobenius a b S hspan hS
  refine ⟨j, fun x => ?_⟩
  have hx := hj x
  change c⁻¹ * T x = x ^ (Fintype.card F ^ j) at hx
  rw [← hx, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end NSDensity
