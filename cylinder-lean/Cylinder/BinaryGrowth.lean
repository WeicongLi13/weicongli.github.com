module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
namespace Cylinder.BinaryGrowth
open Polynomial Module
variable {K : Type*} [Field K]

/-- Actual multiplication by the polynomial variable, as a scalar-linear map. -/
def mulX : K[X] →ₗ[K] K[X] := LinearMap.mul K K[X] X

@[simp] theorem mulX_apply (p : K[X]) : mulX p = X * p := rfl

theorem mulX_injective : Function.Injective (mulX (K := K)) := by
  intro p q h
  exact mul_left_cancel₀ (Polynomial.X_ne_zero) h

/-- A nonzero finite-dimensional polynomial subspace has an actual element
of maximum degree. This is proved from finite generation, not an echelon hypothesis. -/
theorem exists_max_degree (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥) :
    ∃ p ∈ U, p ≠ 0 ∧ ∀ q ∈ U, q.natDegree ≤ p.natDegree := by
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp inferInstance : U.FG)
  have hsne : s.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    apply hU
    simpa [hn] using hspan.symm
  obtain ⟨p, hp, hmax⟩ := Polynomial.exists_degree_le_of_mem_span_of_finite hs hsne
  have hpU : p ∈ U := hspan ▸ Submodule.subset_span hp
  obtain ⟨q, hqU, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hp0 : p ≠ 0 := by
    intro hz
    have hh := hmax q (hspan.symm ▸ hqU)
    rw [hz, degree_zero, le_bot_iff, degree_eq_bot] at hh
    exact hq0 hh
  refine ⟨p, hpU, hp0, fun q hq => ?_⟩
  exact natDegree_le_of_degree_le ((hmax q (hspan.symm ▸ hq)).trans degree_le_natDegree)

/-- Multiplication by X cannot preserve a nonzero finite-dimensional subspace. -/
theorem mulX_map_not_le (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥) : ¬ U.map mulX ≤ U := by
  obtain ⟨p, hp, hp0, hmax⟩ := exists_max_degree U hU
  intro hle
  have hx : X * p ∈ U := hle (Submodule.mem_map_of_mem hp)
  have hh := hmax (X * p) hx
  rw [natDegree_X_mul hp0] at hh
  omega

/-- The dehomogenized growth inequality for the actual polynomial ring. -/
theorem finrank_growth (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥) :
    finrank K U + 1 ≤ finrank K ↥(U ⊔ U.map mulX) := by
  apply Nat.succ_le_of_lt
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  exact mulX_map_not_le U hU (sup_eq_left.mp heq.symm)

end Cylinder.BinaryGrowth



