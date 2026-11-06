module

public import Cylinder.BMMBlockerPairs

/-! The algebra used to normalize secant coefficients after the geometric
cocycle identity has been proved. This file does not prove that identity. -/

@[expose] public section
noncomputable section

namespace Cylinder.BMMCocycleNormalization

variable {K ι : Type*} [Field K]

theorem cocycle_all_of_distinct (c : ι → ι → K)
    (hdiag : ∀ i, c i i = 1) (hreverse : ∀ i j, c i j * c j i = 1)
    (htriangle : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → c i j * c j k * c k i = 1) :
    ∀ i j k, c i j * c j k * c k i = 1 := by
  intro i j k
  by_cases hij : i = j
  · subst j
    rw [hdiag, one_mul, hreverse]
  by_cases hjk : j = k
  · subst k
    rw [hdiag, mul_one, hreverse]
  by_cases hki : k = i
  · subst k
    rw [hdiag, mul_one, hreverse]
  exact htriangle i j k hij hjk hki

theorem coefficients_ne_zero (c : ι → ι → K)
    (hreverse : ∀ i j, c i j * c j i = 1) (i j : ι) : c i j ≠ 0 := by
  intro hzero
  have h := hreverse i j
  rw [hzero, zero_mul] at h
  exact zero_ne_one h

theorem anchor_coefficients (c : ι → ι → K) (a : ι)
    (hreverse : ∀ i j, c i j * c j i = 1)
    (hcocycle : ∀ i j k, c i j * c j k * c k i = 1) (i j : ι) :
    c a i * c i j = c a j := by
  apply mul_right_cancel₀ (coefficients_ne_zero c hreverse j a)
  rw [hcocycle, hreverse]

theorem exists_normalizing_weights (c : ι → ι → K) (a : ι)
    (hdiag : ∀ i, c i i = 1) (hreverse : ∀ i j, c i j * c j i = 1)
    (htriangle : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → c i j * c j k * c k i = 1) :
    ∃ α : ι → K, α a = 1 ∧ (∀ i, α i ≠ 0) ∧ ∀ i j, c i j = α j / α i := by
  refine ⟨c a, hdiag a, fun i => coefficients_ne_zero c hreverse a i, ?_⟩
  intro i j
  apply (eq_div_iff (coefficients_ne_zero c hreverse a i)).mpr
  rw [mul_comm]
  exact anchor_coefficients c a hreverse (cocycle_all_of_distinct c hdiag hreverse htriangle) i j

theorem normalized_secant_formula {V : Type*} [AddCommGroup V] [Module K V]
    (E : ι → V) (α : ι → K) (hα : ∀ i, α i ≠ 0)
    (c : ι → ι → K) (hc : ∀ i j, c i j = α j / α i) (i j : ι) :
    E i + c i j • E j = (α i)⁻¹ • (α i • E i + α j • E j) := by
  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (hα i), one_smul, hc]
  rw [div_eq_mul_inv, mul_comm]

end Cylinder.BMMCocycleNormalization

end
