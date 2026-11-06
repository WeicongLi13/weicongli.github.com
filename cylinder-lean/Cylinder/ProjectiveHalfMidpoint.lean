module

public import Cylinder.ProjectiveMidpointRecovery

/-! The true four-point set with affine coordinates infinity, zero,
one and one half satisfies the finite-set midpoint identity. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveHalfMidpoint

open Cylinder.RationalPlaneLine Cylinder.LineAffineCoordinates

variable {K : Type*} [Field K]

theorem four_point_half_midpoint (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (B : Finset (PlanePoint K)) (hB : B.card = 4) (R C₀ C₁ D : PlanePoint K)
    (hRB : R ∈ B) (hC₀B : C₀ ∈ B) (hC₁B : C₁ ∈ B) (hDB : D ∈ B)
    (u₀ u₁ uD : K) (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (huD : uD ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (hR : g R.rep = ![0, 0, 1])
    (hC₀ : g C₀.rep = u₀ • ![0, 1, 0])
    (hC₁ : g C₁.rep = u₁ • ![0, 1, 1])
    (hD : g D.rep = uD • ![0, 1, (2 : K)⁻¹]) :
    D ∈ B.erase R ∧ (B.erase R).erase D = {C₀, C₁} ∧
      (∑ P ∈ (B.erase R).erase D, lineParameter g P) = 2 * lineParameter g D := by
  have hp₀ : lineParameter g C₀ = 0 := by simp [lineParameter, hC₀]
  have hp₁ : lineParameter g C₁ = -1 := by
    simp [lineParameter, hC₁, hu₁]
  have hpD : lineParameter g D = -(2 : K)⁻¹ := by
    rw [lineParameter, hD]
    change -(uD * (2 : K)⁻¹) / (uD * 1) = -(2 : K)⁻¹
    field_simp
  have hhalf0 : (2 : K)⁻¹ ≠ 0 := inv_ne_zero htwo
  have hhalf1 : (2 : K)⁻¹ ≠ 1 := by
    intro heq
    have he := mul_inv_cancel₀ htwo
    rw [heq, mul_one] at he
    have hz : (1 : K) = 0 := by linear_combination he
    exact one_ne_zero hz
  have hC₀R : C₀ ≠ R := by
    intro heq
    have he := congrFun (hC₀.symm.trans (heq ▸ hR)) 1
    exact hu₀ (by simpa using he)
  have hC₁R : C₁ ≠ R := by
    intro heq
    have he := congrFun (hC₁.symm.trans (heq ▸ hR)) 1
    exact hu₁ (by simpa using he)
  have hDR : D ≠ R := by
    intro heq
    have he := congrFun (hD.symm.trans (heq ▸ hR)) 1
    exact huD (by simpa using he)
  have h01 : C₀ ≠ C₁ := by
    intro heq
    have he := congrArg (lineParameter g) heq
    rw [hp₀, hp₁] at he
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0)) he.symm
  have h0D : C₀ ≠ D := by
    intro heq
    have he := congrArg (lineParameter g) heq
    rw [hp₀, hpD] at he
    exact (neg_ne_zero.mpr hhalf0) he.symm
  have h1D : C₁ ≠ D := by
    intro heq
    have he := congrArg (lineParameter g) heq
    rw [hp₁, hpD] at he
    exact hhalf1 (neg_inj.mp he).symm
  have hset : B = {R, C₀, C₁, D} := by
    have hsub : ({R, C₀, C₁, D} : Finset (PlanePoint K)) ⊆ B := by
      intro P hP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({R, C₀, C₁, D} : Finset (PlanePoint K)).card = 4 := by
      simp [Ne.symm hC₀R, Ne.symm hC₁R, Ne.symm hDR, h01, h0D, h1D]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have herase : (B.erase R).erase D = {C₀, C₁} := by
    rw [hset]
    ext P
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  refine ⟨Finset.mem_erase.mpr ⟨hDR, hDB⟩, herase, ?_⟩
  rw [herase, Finset.sum_pair h01, hp₀, hp₁, hpD]
  simp [htwo]

end Cylinder.ProjectiveHalfMidpoint

end
