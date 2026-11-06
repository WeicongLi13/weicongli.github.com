import NSDensity.StandardGroup

open scoped BigOperators

namespace NSDensity

variable {F E I : Type*} [Field F] [Field E] [Algebra F E] [Fintype I]

/-- The linear group permuting the given finite collection of columns. -/
def columnLinearGroup (v : I → E) : Subgroup (E ≃ₗ[F] E) where
  carrier := {T | ∃ σ : Equiv.Perm I, ∀ i, T (v i) = v (σ i)}
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro T U ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, fun i => by simp only [LinearEquiv.mul_apply, hτ, hσ,
      Equiv.Perm.mul_apply]⟩
  inv_mem' := by
    rintro T ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun i => ?_⟩
    apply T.injective
    change T (T.symm (v i)) = T (v (σ.symm i))
    rw [T.apply_symm_apply, hσ, σ.apply_symm_apply]

theorem mem_columnLinearGroup_iff (v : I → E) (hv : Function.Injective v)
    (T : E ≃ₗ[F] E) :
    T ∈ columnLinearGroup (F := F) v ↔ ∀ i, T (v i) ∈ Set.range v := by
  constructor
  · rintro ⟨σ, hσ⟩ i
    exact ⟨σ i, (hσ i).symm⟩
  · intro h
    classical
    let f : I → I := fun i => Classical.choose (h i)
    have hf (i : I) : v (f i) = T (v i) := Classical.choose_spec (h i)
    have hinj : Function.Injective f := by
      intro i j hij
      apply hv
      apply T.injective
      rw [← hf, ← hf, hij]
    let σ : Equiv.Perm I := Equiv.ofBijective f
      ⟨hinj, Finite.surjective_of_injective hinj⟩
    exact ⟨σ, fun i => (hf i).symm⟩

/-- Permutations preserving all linear relations among the columns. -/
def columnRelationGroup (v : I → E) : Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀ c : I → F,
    columnEvalOver v c = 0 ↔ columnEvalOver v (c ∘ σ) = 0}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ c
    exact (hσ c).trans (hτ (c ∘ σ))
  inv_mem' := by
    intro σ hσ c
    simpa [Function.comp_def] using (hσ (c ∘ σ.symm)).symm

noncomputable def columnPermutation (v : I → E)
    (T : columnLinearGroup (F := F) v) : Equiv.Perm I :=
  Classical.choose T.property

omit [Fintype I] in
theorem columnPermutation_apply (v : I → E)
    (T : columnLinearGroup (F := F) v) (i : I) :
    T.val (v i) = v (columnPermutation v T i) :=
  Classical.choose_spec T.property i

noncomputable def columnPermutationHom (v : I → E) (hv : Function.Injective v) :
    columnLinearGroup (F := F) v →* Equiv.Perm I where
  toFun := columnPermutation v
  map_one' := by
    apply Equiv.ext
    intro i
    apply hv
    exact (columnPermutation_apply v 1 i).symm
  map_mul' T U := by
    apply Equiv.ext
    intro i
    apply hv
    rw [← columnPermutation_apply v (T * U) i]
    change T.val (U.val (v i)) = v (columnPermutation v T (columnPermutation v U i))
    rw [columnPermutation_apply v U i, columnPermutation_apply v T]

theorem mem_columnRelationGroup_of_linearEquiv (v : I → E)
    (T : E ≃ₗ[F] E) (σ : Equiv.Perm I) (hT : ∀ i, T (v i) = v (σ i)) :
    σ ∈ columnRelationGroup (F := F) v := by
  have hTi (i : I) : T.symm (v i) = v (σ.symm i) := by
    apply T.injective
    rw [T.apply_symm_apply, hT, σ.apply_symm_apply]
  intro c
  have heq : T.symm (columnEvalOver v c) = columnEvalOver v (c ∘ σ) := by
    rw [columnEvalOver_permute]
    change T.symm (∑ i, c i • v i) = ∑ i, c i • v (σ.symm i)
    simp only [map_sum, map_smul, hTi]
  rw [← heq]
  exact T.symm.map_eq_zero_iff.symm

noncomputable def columnAutHom (v : I → E) (hv : Function.Injective v) :
    columnLinearGroup (F := F) v →* columnRelationGroup (F := F) v :=
  (columnPermutationHom v hv).codRestrict (columnRelationGroup (F := F) v)
    (fun T => mem_columnRelationGroup_of_linearEquiv v T.val
      (columnPermutation v T) (columnPermutation_apply v T))

theorem linearEquiv_ext_columns (v : I → E)
    (hspan : Function.Surjective (columnEvalOver (F := F) v))
    {T U : E ≃ₗ[F] E} (h : ∀ i, T (v i) = U (v i)) : T = U := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨c, rfl⟩ := hspan x
  change T (∑ i, c i • v i) = U (∑ i, c i • v i)
  simp only [map_sum, map_smul, h]

theorem columnAutHom_injective (v : I → E) (hv : Function.Injective v)
    (hspan : Function.Surjective (columnEvalOver (F := F) v)) :
    Function.Injective (columnAutHom (F := F) v hv) := by
  intro T U h
  apply Subtype.ext
  apply linearEquiv_ext_columns v hspan
  intro i
  have hperm : columnPermutation v T = columnPermutation v U := congrArg Subtype.val h
  rw [columnPermutation_apply, columnPermutation_apply, hperm]

theorem columnAutHom_surjective [Finite E] (v : I → E) (hv : Function.Injective v)
    (hspan : Function.Surjective (columnEvalOver (F := F) v)) :
    Function.Surjective (columnAutHom (F := F) v hv) := by
  intro σ
  have hinv := (columnRelationGroup (F := F) v).inv_mem σ.property
  obtain ⟨T, hT⟩ := exists_column_linearEquiv_over v hspan σ.val.symm hinv
  simp only [Equiv.symm_symm] at hT
  let T' : columnLinearGroup (F := F) v := ⟨T, σ.val, hT⟩
  refine ⟨T', ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply hv
  change v (columnPermutation v T' i) = v (σ.val i)
  rw [← columnPermutation_apply v T' i]
  exact hT i

/-- The actual group isomorphism between linear column symmetries and
coordinate permutation automorphisms, for distinct spanning columns. -/
noncomputable def columnLinearGroupEquiv [Finite E] (v : I → E)
    (hv : Function.Injective v)
    (hspan : Function.Surjective (columnEvalOver (F := F) v)) :
    columnLinearGroup (F := F) v ≃* columnRelationGroup (F := F) v :=
  MulEquiv.ofBijective (columnAutHom v hv)
    ⟨columnAutHom_injective v hv hspan, columnAutHom_surjective v hv hspan⟩

theorem columnLinearGroupEquiv_apply_column [Finite E] (v : I → E)
    (hv : Function.Injective v)
    (hspan : Function.Surjective (columnEvalOver (F := F) v))
    (T : columnLinearGroup (F := F) v) (i : I) :
    T.val (v i) = v ((columnLinearGroupEquiv v hv hspan T).val i) :=
  columnPermutation_apply v T i

/-- In the root-column model the standard coordinate permutations correspond
exactly to multiplication by a root power followed by a Frobenius power. -/
theorem columnPermutation_standard_iff [Fintype F] [Finite E]
    {n : ℕ} {a : E} (hn : 0 < n) (ha : orderOf a = n)
    (hspan : Function.Surjective
      (columnEvalOver (F := F) (fun i : Fin n => a ^ i.val)))
    (T : columnLinearGroup (F := F) (fun i : Fin n => a ^ i.val)) :
    Concrete.standardPermutation (Fintype.card F) n
        (columnPermutation (fun i : Fin n => a ^ i.val) T) ↔
      ∃ (j : ℕ) (b : ZMod n), ∀ x : E,
        T.val x = a ^ b.val * x ^ (Fintype.card F ^ j) := by
  let : NeZero n := ⟨hn.ne'⟩
  constructor
  · rintro ⟨j, b, hσ⟩
    have ha0 : a ≠ 0 := (orderOf_pos_iff.mp (ha.symm ▸ hn)).isUnit.ne_zero
    let e : E ≃ₐ[F] E := FiniteField.frobeniusAlgEquivOfAlgebraic F E ^ j
    let S : E ≃ₗ[F] E := e.toLinearEquiv.trans
      ((LinearEquiv.smulOfNeZero E E (a ^ b.val) (pow_ne_zero _ ha0)).restrictScalars F)
    have hS (x : E) : S x = a ^ b.val * x ^ (Fintype.card F ^ j) := by
      change a ^ b.val * e x = _
      simp only [e, AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    have hTS : T.val = S := by
      apply linearEquiv_ext_columns _ hspan
      intro i
      rw [columnPermutation_apply, hS, ← pow_mul, ← pow_add]
      apply (Concrete.root_pow_eq_iff_zmod hn ha).2
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_comm, add_comm] using hσ i
    exact ⟨j, b, fun x => hTS ▸ hS x⟩
  · rintro ⟨j, b, hT⟩
    refine ⟨j, b, fun i => ?_⟩
    have heq := (columnPermutation_apply (fun i : Fin n => a ^ i.val) T i).symm.trans
      (hT (a ^ i.val))
    rw [← pow_mul, ← pow_add] at heq
    have hc := (Concrete.root_pow_eq_iff_zmod hn ha).1 heq
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_comm, add_comm] using hc

end NSDensity

namespace NSDensity.Concrete

variable {E I : Type*} [Field E] [Fintype I]

theorem columnRelationGroup_eq_permutationAutGroup (F : Subfield E) (v : I → E) :
    columnRelationGroup (F := F) v = permutationAutGroup F v := by
  ext σ
  rfl

/-- The group isomorphism for the actual relation code used in the paper. -/
noncomputable def columnLinearGroupEquiv_permutationAutGroup [Finite E]
    (F : Subfield E) (v : I → E) (hv : Function.Injective v)
    (hspan : Function.Surjective (columnEval F v)) :
    columnLinearGroup (F := F) v ≃* permutationAutGroup F v :=
  (columnLinearGroupEquiv v hv hspan).trans
    (MulEquiv.subgroupCongr (columnRelationGroup_eq_permutationAutGroup F v))

variable [Finite E]

theorem rootField_columnRelationGroup_eq (F : Subfield E) (n : ℕ) (a : E) :
    columnRelationGroup (F := F)
        (fun i : Fin n => (rootInField F a) ^ i.val) =
      permutationAutGroup F (fun i : Fin n => a ^ i.val) := by
  have heval (c : Fin n → F) :
      columnEvalOver (fun i : Fin n => (rootInField F a) ^ i.val) c = 0 ↔
        c ∈ relationCode F (fun i : Fin n => a ^ i.val) := by
    rw [← Subtype.coe_inj]
    change ((∑ i, c i • (rootInField F a) ^ i.val : rootField F a) : E) = 0 ↔ _
    simp [relationCode, rootInField, Algebra.smul_def]
    rfl
  ext σ
  constructor
  · intro h c
    exact (heval c).symm.trans ((h c).trans (heval (c ∘ σ)))
  · intro h c
    exact (heval c).trans ((h c).trans (heval (c ∘ σ)).symm)

theorem rootField_columns_injective (F : Subfield E) {n : ℕ} {a : E}
    (ha : orderOf a = n) :
    Function.Injective (fun i : Fin n => (rootInField F a) ^ i.val) := by
  intro i j hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := rootInField F a)
  · simp [rootInField_orderOf, ha]
  · simp [rootInField_orderOf, ha]
  · exact hij

theorem rootField_columns_span (F : Subfield E) {n : ℕ} {a : E}
    (hn : 0 < n) (ha : orderOf a = n) :
    Function.Surjective (columnEvalOver (F := F)
      (fun i : Fin n => (rootInField F a) ^ i.val)) :=
  columnEvalOver_surjective_of_powers_span hn ((rootInField_orderOf F a).trans ha)
    (rootInField_powers_span F a)

/-- The ambient field need not be generated by the root: use its generated
field as the linear model and the original coordinate code as the target. -/
noncomputable def rootLinearGroupEquiv_permutationAutGroup
    (F : Subfield E) {n : ℕ} {a : E} (hn : 0 < n) (ha : orderOf a = n) :
    columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val) ≃*
      permutationAutGroup F (fun i : Fin n => a ^ i.val) :=
  (columnLinearGroupEquiv _ (rootField_columns_injective F ha)
    (rootField_columns_span F hn ha)).trans
      (MulEquiv.subgroupCongr (rootField_columnRelationGroup_eq F n a))

theorem rootLinearGroupEquiv_standard_iff
    (F : Subfield E) [Fintype F] {n : ℕ} {a : E} (hn : 0 < n) (ha : orderOf a = n)
    (T : columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val)) :
    standardPermutation (Fintype.card F) n
        (rootLinearGroupEquiv_permutationAutGroup F hn ha T).val ↔
      ∃ (j : ℕ) (b : ZMod n), ∀ x : rootField F a,
        T.val x = (rootInField F a) ^ b.val * x ^ (Fintype.card F ^ j) :=
  columnPermutation_standard_iff hn ((rootInField_orderOf F a).trans ha)
    (rootField_columns_span F hn ha) T

#print axioms columnLinearGroupEquiv_permutationAutGroup
#print axioms rootLinearGroupEquiv_permutationAutGroup
#print axioms rootLinearGroupEquiv_standard_iff

end NSDensity.Concrete
