module

public import Cylinder.JetIdeal
public import Cylinder.FrobeniusPolar

/-! Actual independent first-jet conditions at every rational curve point. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.PolarJetConditions

open MvPolynomial Module Cylinder.JetEvaluation Cylinder.JetIdeal Cylinder.FrobeniusPolar

variable {K : Type*} [Field K]

def tangentFunctional (F : MvPolynomial (Fin 3) K) (v : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K where
  toFun w := ∑ i : Fin 3, eval v (pderiv i F) * w i
  map_add' w z := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a w := by simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem tangentFunctional_eq_directional (F : MvPolynomial (Fin 3) K) (v w : Fin 3 → K) :
    tangentFunctional F v w = eval v (directional w F) := by
  simp [tangentFunctional, directional, smul_eq_mul, mul_comm]

theorem tangentFunctional_radial_zero (F : MvPolynomial (Fin 3) K) (n : ℕ)
    (hF : F.IsHomogeneous n) (v : Fin 3 → K) (hzero : eval v F = 0) :
    tangentFunctional F v v = 0 := by
  have h := congrArg (eval v) hF.sum_X_mul_pderiv
  simpa [tangentFunctional, hzero, mul_comm] using h

/-- A plane tangent kernel always has a direction independent of the radial line. -/
theorem exists_nonradial_in_kernel (f : (Fin 3 → K) →ₗ[K] K)
    (v : Fin 3 → K) (hv : v ≠ 0) :
    ∃ w : Fin 3 → K, f w = 0 ∧ Nonradial v w := by
  have hk : 2 ≤ finrank K (LinearMap.ker f) := by
    have hr := (LinearMap.range f).finrank_le
    have h := f.finrank_range_add_finrank_ker
    simp only [Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hr h
    omega
  have hnotle : ¬ LinearMap.ker f ≤ K ∙ v := by
    intro hle
    have h := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv] at h
    omega
  obtain ⟨w, hw, hnot⟩ : ∃ w, w ∈ LinearMap.ker f ∧ w ∉ K ∙ v := by
    by_contra hn
    push Not at hn
    exact hnotle hn
  refine ⟨w, LinearMap.mem_ker.mp hw, ?_⟩
  intro a ha
  apply hnot
  rw [ha]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v)

variable (p : ℕ) [CharP K p]

theorem directional_polar_at_fixed (n : ℕ) (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous n) (v w : Fin 3 → K) (hv : FrobeniusFixed p v) :
    eval v (directional w (polar p F)) = ((n - 1 : ℕ) : K) * eval v (directional w F) := by
  rw [← tangentFunctional_eq_directional, ← tangentFunctional_eq_directional]
  have hg := gradient_polar_at_fixed p n F hF v hv
  have hgi (i : Fin 3) : eval v (pderiv i (polar p F)) =
      ((n - 1 : ℕ) : K) * eval v (pderiv i F) := by
    simpa only [gradient, Pi.smul_apply, nsmul_eq_mul] using congrFun hg i
  change (∑ i : Fin 3, eval v (pderiv i (polar p F)) * w i) =
    ((n - 1 : ℕ) : K) * ∑ i : Fin 3, eval v (pderiv i F) * w i
  simp only [hgi, mul_assoc, Finset.mul_sum]

/-- Every rational point, including a singular point, has a nonradial first
jet annihilating both the curve equation and its polar. -/
theorem exists_polar_jet_direction (n : ℕ) (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous n) (v : Fin 3 → K) (hv : v ≠ 0)
    (hfixed : FrobeniusFixed p v) (hzero : eval v F = 0) :
    ∃ w : Fin 3 → K, Nonradial v w ∧ eval v (directional w F) = 0 ∧
      eval v (polar p F) = 0 ∧ eval v (directional w (polar p F)) = 0 := by
  obtain ⟨w, hw, hnonradial⟩ := exists_nonradial_in_kernel (tangentFunctional F v) v hv
  have hD : eval v (directional w F) = 0 := by
    rwa [← tangentFunctional_eq_directional]
  refine ⟨w, hnonradial, hD, polar_vanishes_at_rational_zero p n F hF v hfixed hzero, ?_⟩
  rw [directional_polar_at_fixed p n F hF v w hfixed, hD, mul_zero]

theorem exists_polar_firstJetIdeal {I : Type*} (n : ℕ)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous n) (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hfixed : ∀ i, FrobeniusFixed p (v i))
    (hzero : ∀ i, eval (v i) F = 0) :
    ∃ w : I → Fin 3 → K, (∀ i, Nonradial (v i) (w i)) ∧
      Ideal.span {F, polar p F} ≤ firstJetIdeal v w := by
  choose w hn hD hp hDp using fun i => exists_polar_jet_direction p n F hF
    (v i) (hv i) (hfixed i) (hzero i)
  exact ⟨w, hn, span_pair_le_firstJetIdeal v w F (polar p F)
    (fun i => ⟨hzero i, hD i⟩) (fun i => ⟨hp i, hDp i⟩)⟩

/-- A genuine quotient dimension lower bound for every finite rational
point set on the curve. Its complete-intersection upper bound is separate. -/
theorem polar_two_card_le_graded_quotient {I : Type*} [Fintype I] [Infinite K]
    (n : ℕ) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous n)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : Cylinder.HilbertEvaluation.ProjectivelyDistinct v)
    (hfixed : ∀ i, FrobeniusFixed p (v i)) (hzero : ∀ i, eval (v i) F = 0)
    (d : ℕ) (hd : 2 * Fintype.card I - 1 ≤ d) :
    2 * Fintype.card I ≤ finrank K
      (Cylinder.HilbertEvaluation.Forms K d ⧸ JetIdeal.idealPiece (Ideal.span {F, polar p F}) d) := by
  obtain ⟨w, hw, hJ⟩ := exists_polar_firstJetIdeal p n F hF v hv hfixed hzero
  exact two_card_le_graded_quotient v w hv hsep hw (Ideal.span {F, polar p F}) hJ d hd

end Cylinder.PolarJetConditions

end
