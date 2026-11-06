import NSDensity.CodeModelAffine
import NSDensity.CodeModelColumns

open scoped BigOperators

namespace NSDensity.Concrete

variable {E : Type*} [Field E]

/-- Equality of powers of a root of exact order n is equality of exponents
in Z/nZ. This also handles the degenerate root of order one. -/
theorem root_pow_eq_iff_zmod {a : E} {n k l : ℕ} (hn : 0 < n)
    (ha : orderOf a = n) :
    a ^ k = a ^ l ↔ (k : ZMod n) = (l : ZMod n) := by
  have hf : IsOfFinOrder a := orderOf_pos_iff.mp (ha.symm ▸ hn)
  rw [ZMod.natCast_eq_natCast_iff]
  simpa only [ha] using hf.pow_eq_pow_iff_modEq (n := k) (m := l)

/-- The ordinary cyclic-shift/Frobenius permutation group. -/
def standardPermutation (q n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (j : ℕ) (b : ZMod n),
    ∀ i : Fin n, ((σ i).val : ZMod n) = (q : ZMod n) ^ j * (i.val : ZMod n) + b

theorem powers_span_of_columnEval_surjective (F : Subfield E) {a : E} {n : ℕ}
    (hspan : Function.Surjective (columnEval F (fun i : Fin n => a ^ i.val))) :
    Submodule.span F (Set.range fun k : ℕ => a ^ k) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨c, rfl⟩ := hspan x
  change (∑ i, (c i : E) * a ^ i.val) ∈ _
  apply Submodule.sum_mem
  intro i _
  change c i • a ^ i.val ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.val, rfl⟩)

/-- Affine rigidity in any generated field: a linear transformation inducing
an affine permutation on the root powers induces a standard permutation. -/
theorem linearEquiv_affine_powers_is_standard {F : Type*} [Field F] [Fintype F]
    [Algebra F E] [Finite E]
    {a : E} {n : ℕ} (hn : 0 < n) (ha : orderOf a = n)
    (hspan : Submodule.span F (Set.range fun k : ℕ => a ^ k) = ⊤)
    (T : E ≃ₗ[F] E) (σ : Equiv.Perm (Fin n))
    (hT : ∀ i : Fin n, T (a ^ i.val) = a ^ (σ i).val)
    (hAffine : affinePermutation n σ) : standardPermutation (Fintype.card F) n σ := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨u, b, hAffine⟩ := hAffine
  have hapow : a ≠ 0 := (orderOf_pos_iff.mp (ha.symm ▸ hn)).isUnit.ne_zero
  have hAll : ∀ k : ℕ, T (a ^ k) = a ^ b.val * (a ^ (u : ZMod n).val) ^ k := by
    intro k
    let i : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩
    have hi : a ^ i.val = a ^ k := by
      simpa only [i, ha] using pow_mod_orderOf a k
    rw [← hi, hT]
    rw [← pow_mul, ← pow_add]
    apply (root_pow_eq_iff_zmod hn ha).2
    rw [hAffine]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    simp [i, ZMod.natCast_mod, add_comm]
  obtain ⟨j, hj⟩ := linearEquiv_scaled_powers_eq_standard a
    (a ^ (u : ZMod n).val) (a ^ b.val) (pow_ne_zero _ hapow) T
    hspan hAll
  refine ⟨j, b, fun i => ?_⟩
  have heq : a ^ (σ i).val = a ^ b.val * (a ^ i.val) ^ (Fintype.card F ^ j) := by
    rw [← hT i]
    exact hj _
  rw [← pow_mul, ← pow_add] at heq
  have hc := (root_pow_eq_iff_zmod hn ha).1 heq
  simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_comm, add_comm] using hc

/-- In the full column-span model, every affine automorphism of the actual
relation code is a standard shift/Frobenius permutation. -/
theorem affine_preservesRelations_is_standard [Finite E] (F : Subfield E) [Fintype F]
    {a : E} {n : ℕ} (hn : 0 < n) (ha : orderOf a = n)
    (hspan : Function.Surjective (columnEval F (fun i : Fin n => a ^ i.val)))
    (σ : Equiv.Perm (Fin n))
    (hσ : preservesRelations F (fun i : Fin n => a ^ i.val) σ)
    (hAffine : affinePermutation n σ) : standardPermutation (Fintype.card F) n σ := by
  have hinv : preservesRelations F (fun i : Fin n => a ^ i.val) σ.symm :=
    (permutationAutGroup F (fun i : Fin n => a ^ i.val)).inv_mem hσ
  obtain ⟨T, hT⟩ := exists_column_linearEquiv_apply F _ hspan σ.symm hinv
  simp only [Equiv.symm_symm] at hT
  exact linearEquiv_affine_powers_is_standard hn ha
    (powers_span_of_columnEval_surjective F hspan) T σ hT hAffine

end NSDensity.Concrete
