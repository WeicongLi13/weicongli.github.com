module

public import Mathlib.LinearAlgebra.Vandermonde
public meta import Lean.Elab.Tactic.Omega

/-!
# The Vandermonde step for a nonempty projection ray

Distinct ray parameters and vanishing moments force all coefficients to
vanish if the number of equations reaches the ray size. Thus a full
support relation with moments through degree `N` needs at least `N + 2`
points on every nonempty ray.

The geometric derivation of these moment equations from projective
evaluation relations is a separate step; it is not assumed to be verified
by this module.
-/

@[expose] public section

namespace Cylinder.VandermondeMoments

open scoped BigOperators

variable {K : Type*} [Field K] {r : ℕ}

theorem coefficients_eq_zero_of_moments (t c : Fin r → K)
    (ht : Function.Injective t)
    (hm : ∀ j : ℕ, j < r → (∑ i : Fin r, c i * t i ^ j) = 0) : c = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht
  intro j
  exact hm j.val j.isLt

/-- A nonempty ray whose coefficients are all nonzero cannot have at
most `N + 1` points when its first `N + 1` moments vanish. -/
theorem ray_size_lower_bound (t c : Fin r → K) (hr : 0 < r)
    (ht : Function.Injective t) (hc : ∀ i, c i ≠ 0)
    (N : ℕ) (hm : ∀ j : ℕ, j ≤ N → (∑ i : Fin r, c i * t i ^ j) = 0) :
    N + 2 ≤ r := by
  by_contra hsmall
  have hz : c = 0 := coefficients_eq_zero_of_moments t c ht
    (fun j hj => hm j (by omega))
  let i : Fin r := ⟨0, hr⟩
  exact hc i (congrFun hz i)

theorem ray_size_lower_bound_of_degree (t c : Fin r → K) (hr : 0 < r)
    (ht : Function.Injective t) (hc : ∀ i, c i ≠ 0)
    (d a : ℕ)
    (hm : ∀ j : ℕ, j ≤ d - a → (∑ i : Fin r, c i * t i ^ j) = 0) :
    d - a + 2 ≤ r := by
  exact ray_size_lower_bound t c hr ht hc (d - a) hm

end Cylinder.VandermondeMoments
