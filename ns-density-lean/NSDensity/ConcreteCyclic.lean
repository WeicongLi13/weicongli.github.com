import NSDensity.ConcreteDuality
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Cyclicity, nonzero words, and nondegeneracy of the root-column code. -/

open scoped BigOperators

namespace NSDensity.Concrete

variable {E : Type*} [Field E] {I : Type*} [Fintype I]

omit [Fintype I] in
/-- An invertible linear map that permutes the columns induces a genuine
permutation automorphism of the corresponding generator-matrix code. -/
theorem preservesCode_of_column_equiv (F : Subfield E) (v : I → E)
    (σ : Equiv.Perm I) (T : E ≃ₗ[F] E) (hT : ∀ i, T (v i) = v (σ i)) :
    preservesCode F (functionalCode F v) σ := by
  have hTinv (i : I) : T.symm (v i) = v (σ.symm i) := by
    apply T.injective
    rw [T.apply_symm_apply, hT, σ.apply_symm_apply]
  intro c
  constructor
  · intro hc
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v c).1 hc
    refine (mem_functionalCode F v (c ∘ σ)).2 ⟨φ.comp T.toLinearMap, fun i => ?_⟩
    change φ (T (v i)) = c (σ i)
    rw [hT, hφ]
  · intro hc
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v (c ∘ σ)).1 hc
    refine (mem_functionalCode F v c).2 ⟨φ.comp T.symm.toLinearMap, fun i => ?_⟩
    change φ (T.symm (v i)) = c i
    rw [hTinv, hφ]
    exact congrArg c (σ.apply_symm_apply i)

omit [Fintype I] in
/-- Different columns are separated by an actual codeword. -/
theorem functionalCode_separates_columns (F : Subfield E) (v : I → E)
    {i j : I} (hij : v i ≠ v j) :
    ∃ w ∈ functionalCode F v, w i ≠ w j := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F (sub_ne_zero.mpr hij)
  refine ⟨functionalEvaluation F v φ, ⟨φ, rfl⟩, ?_⟩
  change φ (v i) ≠ φ (v j)
  intro h
  apply hφ
  rw [map_sub, h, sub_self]

/-- The concrete cyclic code having the consecutive powers of a as columns. -/
def rootFunctionalCode (F : Subfield E) (n : ℕ) (a : E) :
    Submodule F (Fin n → F) := functionalCode F (fun i : Fin n => a ^ i.val)

theorem root_pow_rotate {n : ℕ} (a : E) (hn : 0 < n) (ha : a ^ n = 1)
    (i : Fin n) : a ^ (finRotate n i).val = a ^ i.val * a := by
  cases n with
  | zero => omega
  | succ k =>
    by_cases hi : i = Fin.last k
    · subst i
      simpa [pow_succ] using ha.symm
    · rw [coe_finRotate_of_ne_last hi, pow_succ]

/-- The root-column code is invariant under the cyclic shift. -/
theorem rootFunctionalCode_cyclic (F : Subfield E) {n : ℕ} (a : E)
    (hn : 0 < n) (ha : a ^ n = 1) :
    preservesCode F (rootFunctionalCode F n a) (finRotate n) := by
  have hane : a ≠ 0 := by
    intro h
    simp [h, Nat.ne_of_gt hn] at ha
  let T : E ≃ₗ[F] E :=
    { toFun := fun x => x * a
      invFun := fun x => x * a⁻¹
      left_inv := by intro x; simp [hane]
      right_inv := by intro x; simp [hane]
      map_add' := fun x y => add_mul x y a
      map_smul' := by intro r x; simp [Algebra.smul_def, mul_assoc] }
  exact preservesCode_of_column_equiv F (fun i : Fin n => a ^ i.val) (finRotate n)
    T (fun i => (root_pow_rotate a hn ha i).symm)

/-- The code has a word with a nonzero zeroth coordinate. -/
theorem rootFunctionalCode_has_one (F : Subfield E) {n : ℕ} (a : E)
    (hn : 0 < n) :
    ∃ w ∈ rootFunctionalCode F n a, w ⟨0, hn⟩ = 1 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : E) ≠ 0)
  refine ⟨functionalEvaluation F (fun i : Fin n => a ^ i.val) φ, ⟨φ, rfl⟩, ?_⟩
  simpa using hφ

/-- Exact multiplicative order n prevents any two coordinates from being
identical on the code; this is the nondegeneracy condition. -/
theorem rootFunctionalCode_separates_coordinates (F : Subfield E) {n : ℕ}
    (a : E) (ha : orderOf a = n) {i j : Fin n} (hij : i ≠ j) :
    ∃ w ∈ rootFunctionalCode F n a, w i ≠ w j := by
  apply functionalCode_separates_columns F (fun k : Fin n => a ^ k.val)
  intro h
  apply hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := a)
  · simp [ha]
  · simp [ha]
  · exact h

end NSDensity.Concrete
