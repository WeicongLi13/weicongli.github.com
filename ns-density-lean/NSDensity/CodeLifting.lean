import NSDensity.StandardGroup
import NSDensity.CodeLinearGroup
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

/-!
Lifting preserves the full coordinate automorphism group.
The arithmetic hypothesis on the extension degree is used to prove linear
disjointness; linear disjointness is not an additional external input.
-/

open scoped BigOperators TensorProduct

namespace NSDensity.Concrete

/-- Relations among columns in a field extend over a linearly disjoint
coefficient field. The proof applies scalar extension to the actual
invertible column transformation. -/
theorem preserves_column_relations_of_linearDisjoint
    {F E I : Type*} [Field F] [Field E] [Finite E] [Algebra F E] [Fintype I]
    (A B : IntermediateField F E) (hdisj : A.LinearDisjoint B)
    (v : I → A) (hspan : Function.Surjective (columnEvalOver (F := F) v))
    (σ : Equiv.Perm I)
    (hσ : ∀ c : I → F,
      columnEvalOver v c = 0 ↔ columnEvalOver v (c ∘ σ) = 0) :
    ∀ c : I → B,
      (∑ i, (c i : E) * (v i : E)) = 0 ↔
        (∑ i, (c (σ i) : E) * (v i : E)) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_column_linearEquiv_over v hspan σ hσ
  let μ := B.toSubalgebra.mulMap A.toSubalgebra
  have hμ : Function.Injective μ :=
    (IntermediateField.linearDisjoint_iff'.1 hdisj.symm).injective
  let S : B ⊗[F] A ≃ₗ[B] B ⊗[F] A := T.baseChange F B A A
  intro c
  have hzero (d : I → B) :
      (∑ i, (d i : E) * (v i : E)) = 0 ↔
        (∑ i, d i ⊗ₜ[F] v i : B ⊗[F] A) = 0 := by
    have hd : μ (∑ i, d i ⊗ₜ[F] v i) = ∑ i, (d i : E) * (v i : E) := by
      rw [map_sum]
      rfl
    rw [← hd, ← map_zero μ]
    exact hμ.eq_iff
  rw [hzero c, hzero (fun i => c (σ i))]
  have hsum : S (∑ i, c i ⊗ₜ[F] v i) = ∑ i, c (σ i) ⊗ₜ[F] v i := by
    simp only [map_sum, S, LinearEquiv.baseChange_tmul, hT]
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp σ (fun i => c i ⊗ₜ[F] v (σ.symm i))).symm
  rw [← hsum]
  exact S.map_eq_zero_iff.symm

/-- The finite root field has the expected multiplicative-order degree. -/
theorem rootField_finrank_eq_orderOf
    {F E : Type*} [Field F] [Fintype F] [Field E] [Finite E] [Algebra F E]
    {p e n : ℕ} (hp : p.Prime) (hF : Fintype.card F = p ^ e)
    (hn : 0 < n) (hcop : Nat.Coprime p n) {a : E} (ha : orderOf a = n) :
    Module.finrank F (rootField F a) = orderOf (p ^ e : ZMod n) := by
  let : Fact p.Prime := ⟨hp⟩
  have hroot : IsPrimitiveRoot a n := IsPrimitiveRoot.iff_orderOf.2 ha
  have hdiv : minpoly F a ∣ Polynomial.cyclotomic n F := by
    apply minpoly.dvd
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, Polynomial.IsRoot.def] using
      hroot.isRoot_cyclotomic hn
  have hdeg := Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
    hF hcop hdiv (minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) a))
  have hfield : rootField F a = IntermediateField.adjoin F {a} := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra]
    rfl
  rw [hfield, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := F) a)]
  simpa only [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_pow] using hdeg

/-- Literal equality of automorphism groups over nested coefficient fields
under the lifting hypothesis. -/
theorem lifting_permutationAutGroup_eq
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) :
    permutationAutGroup F (fun i : Fin n => a ^ i.val) =
      permutationAutGroup K (fun i : Fin n => a ^ i.val) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let B : IntermediateField F E :=
    { K with algebraMap_mem' := fun x => hFK x.property }
  let : Fintype B := Fintype.ofFinite B
  have hF' : Fintype.card F = p ^ e := by
    simpa only [Nat.card_eq_fintype_card] using hF
  have hB : Fintype.card B = p ^ (e * t) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hdegree : Module.finrank F B = t := by
    have hcard := Module.card_eq_pow_finrank (K := F) (V := B)
    rw [hF', hB, ← pow_mul] at hcard
    have hmul := Nat.pow_right_injective hp.one_lt hcard
    exact (Nat.eq_of_mul_eq_mul_left he hmul).symm
  let A := rootField F a
  have hA : Module.finrank F A = orderOf (p ^ e : ZMod n) :=
    rootField_finrank_eq_orderOf hp hF' hn hcop ha
  have hdisj : A.LinearDisjoint B :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (by rw [hA, hdegree]; exact hgcd.symm)
  apply le_antisymm
  · intro σ hσ
    let a' : A := rootInField F a
    have ha' : orderOf a' = n := (rootInField_orderOf F a).trans ha
    have hspan := columnEvalOver_surjective_of_powers_span hn ha'
      (rootInField_powers_span F a)
    have hrel : ∀ c : Fin n → F,
        columnEvalOver (fun i : Fin n => a' ^ i.val) c = 0 ↔
          columnEvalOver (fun i : Fin n => a' ^ i.val) (c ∘ σ) = 0 := by
      intro c
      have hcoe (d : Fin n → F) :
          columnEvalOver (fun i : Fin n => a' ^ i.val) d = 0 ↔
            d ∈ relationCode F (fun i : Fin n => a ^ i.val) := by
        rw [← Subtype.coe_inj]
        change ((∑ i, d i • a' ^ i.val : A) : E) = 0 ↔ _
        simp [relationCode, rootInField, a', A, Algebra.smul_def]
        rfl
      exact (hcoe c).trans ((hσ c).trans (hcoe (c ∘ σ)).symm)
    exact preserves_column_relations_of_linearDisjoint A B hdisj
      (fun i : Fin n => a' ^ i.val) hspan σ hrel
  · exact permutationAutGroup_le hFK _

/-- The same lifting identifies the ordinary shift/Frobenius subgroups. -/
theorem lifting_standardPermutation_iff
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) (σ : Equiv.Perm (Fin n)) :
    standardPermutation (p ^ e) n σ ↔ standardPermutation (p ^ (e * t)) n σ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hF' : Fintype.card F = p ^ e := by
    simpa only [Nat.card_eq_fintype_card] using hF
  have hK' : Fintype.card K = p ^ (e * t) := by
    simpa only [Nat.card_eq_fintype_card] using hK
  have hcopF : Nat.Coprime (Fintype.card F) n := by
    rw [hF']; exact hcop.pow_left e
  have hcopK : Nat.Coprime (Fintype.card K) n := by
    rw [hK']; exact hcop.pow_left (e * t)
  have hrel : preservesRelations F (fun i : Fin n => a ^ i.val) σ ↔
      preservesRelations K (fun i : Fin n => a ^ i.val) σ := by
    change σ ∈ permutationAutGroup F _ ↔ σ ∈ permutationAutGroup K _
    rw [lifting_permutationAutGroup_eq F K hFK hp he hF hK hn hcop hgcd ha]
  simpa only [hF', hK'] using
    (standardPermutation_iff_affine_automorphism F hn ha hcopF σ).trans
      ((and_congr hrel Iff.rfl).trans
        (standardPermutation_iff_affine_automorphism K hn ha hcopK σ).symm)

/-- An explicit group isomorphism; its action on coordinate permutations
is the identity. -/
noncomputable def liftingPermutationAutEquiv
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) :
    permutationAutGroup F (fun i : Fin n => a ^ i.val) ≃*
      permutationAutGroup K (fun i : Fin n => a ^ i.val) :=
  MulEquiv.subgroupCongr
    (lifting_permutationAutGroup_eq F K hFK hp he hF hK hn hcop hgcd ha)

theorem liftingPermutationAutEquiv_standard_iff
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n)
    (σ : permutationAutGroup F (fun i : Fin n => a ^ i.val)) :
    standardPermutation (p ^ (e * t)) n
      (liftingPermutationAutEquiv F K hFK hp he hF hK hn hcop hgcd ha σ) ↔
        standardPermutation (p ^ e) n σ :=
  (lifting_standardPermutation_iff F K hFK hp he hF hK hn hcop hgcd ha σ).symm

theorem lifting_standardGroup_eq
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} [NeZero n] (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) :
    standardGroup (p ^ e) (hcop.pow_left e) =
      standardGroup (p ^ (e * t)) (hcop.pow_left (e * t)) := by
  ext σ
  rw [mem_standardGroup_iff, mem_standardGroup_iff]
  exact lifting_standardPermutation_iff F K hFK hp he hF hK (NeZero.pos n) hcop hgcd ha σ

theorem lifting_nonstandardRootCode_iff
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) :
    nonstandardRootCode F n a ↔ nonstandardRootCode K n a := by
  change (∃ σ, σ ∈ permutationAutGroup F (fun i : Fin n => a ^ i.val) ∧
      ¬affinePermutation n σ) ↔
    (∃ σ, σ ∈ permutationAutGroup K (fun i : Fin n => a ^ i.val) ∧
      ¬affinePermutation n σ)
  rw [lifting_permutationAutGroup_eq F K hFK hp he hF hK hn hcop hgcd ha]

/-- The lift as an isomorphism of the actual linear groups on the two
generated root fields, matching the paper's L(n,q) statement. -/
noncomputable def liftingRootLinearGroupEquiv
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n) :
    columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val) ≃*
      columnLinearGroup (F := K) (fun i : Fin n => (rootInField K a) ^ i.val) :=
  (rootLinearGroupEquiv_permutationAutGroup F hn ha).trans
    ((liftingPermutationAutEquiv F K hFK hp he hF hK hn hcop hgcd ha).trans
      (rootLinearGroupEquiv_permutationAutGroup K hn ha).symm)

theorem liftingRootLinearGroupEquiv_permutation
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n)
    (T : columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val)) :
    rootLinearGroupEquiv_permutationAutGroup K hn ha
        (liftingRootLinearGroupEquiv F K hFK hp he hF hK hn hcop hgcd ha T) =
      liftingPermutationAutEquiv F K hFK hp he hF hK hn hcop hgcd ha
        (rootLinearGroupEquiv_permutationAutGroup F hn ha T) := by
  simp only [liftingRootLinearGroupEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

theorem liftingRootLinearGroupEquiv_coordinate_standard_iff
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n)
    (T : columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val)) :
    standardPermutation (p ^ (e * t)) n
        (rootLinearGroupEquiv_permutationAutGroup K hn ha
          (liftingRootLinearGroupEquiv F K hFK hp he hF hK hn hcop hgcd ha T)) ↔
      standardPermutation (p ^ e) n (rootLinearGroupEquiv_permutationAutGroup F hn ha T) := by
  rw [liftingRootLinearGroupEquiv_permutation]
  exact liftingPermutationAutEquiv_standard_iff F K hFK hp he hF hK hn hcop hgcd ha _

/-- The group isomorphism identifies the literal standard linear maps
x ↦ c x^(q^j), not merely an abstract subgroup with the same order. -/
theorem liftingRootLinearGroupEquiv_standard_maps_iff
    {E : Type*} [Field E] [Finite E] (F K : Subfield E) (hFK : F ≤ K)
    {p e t n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hF : Nat.card F = p ^ e) (hK : Nat.card K = p ^ (e * t))
    (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hgcd : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    {a : E} (ha : orderOf a = n)
    (T : columnLinearGroup (F := F) (fun i : Fin n => (rootInField F a) ^ i.val)) :
    (∃ (j : ℕ) (b : ZMod n), ∀ x : rootField K a,
      (liftingRootLinearGroupEquiv F K hFK hp he hF hK hn hcop hgcd ha T).val x =
        (rootInField K a) ^ b.val * x ^ ((p ^ (e * t)) ^ j)) ↔
      ∃ (j : ℕ) (b : ZMod n), ∀ x : rootField F a,
        T.val x = (rootInField F a) ^ b.val * x ^ ((p ^ e) ^ j) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hF' : Fintype.card F = p ^ e := by
    simpa only [Nat.card_eq_fintype_card] using hF
  have hK' : Fintype.card K = p ^ (e * t) := by
    simpa only [Nat.card_eq_fintype_card] using hK
  have hstdF := rootLinearGroupEquiv_standard_iff F hn ha T
  have hstdK := rootLinearGroupEquiv_standard_iff K hn ha
    (liftingRootLinearGroupEquiv F K hFK hp he hF hK hn hcop hgcd ha T)
  rw [hF'] at hstdF
  rw [hK'] at hstdK
  exact hstdK.symm.trans
    ((liftingRootLinearGroupEquiv_coordinate_standard_iff F K hFK hp he hF hK
      hn hcop hgcd ha T).trans hstdF)

#print axioms lifting_permutationAutGroup_eq
#print axioms liftingPermutationAutEquiv_standard_iff
#print axioms liftingRootLinearGroupEquiv_coordinate_standard_iff
#print axioms liftingRootLinearGroupEquiv_standard_maps_iff

end NSDensity.Concrete
