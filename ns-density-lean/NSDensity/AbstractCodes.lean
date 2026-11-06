import NSDensity.CodeFieldTransport
import NSDensity.PaperPairs

namespace NSDensity

/-- An actual arbitrary finite-field cyclic subspace, without a chosen root model. -/
def AbstractNonstandard (n q : ℕ) : Prop :=
  ∃ (F : Type) (fieldF : Field F),
    letI := fieldF
    Finite F ∧ Nat.card F = q ∧ ∃ C : Submodule F (Fin n → F),
      Concrete.irreducibleCyclicCode C ∧ Concrete.nondegenerateCode C ∧
      ∃ σ : Equiv.Perm (Fin n),
        (∀ c : Fin n → F, c ∈ C ↔ (c ∘ σ) ∈ C) ∧
          ¬Concrete.standardPermutation q n σ

theorem paperNonstandard_to_abstract {n q : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime q n) (h : PaperNonstandard n q) : AbstractNonstandard n q := by
  have hc := (codeNonstandard_iff_paper hn hcop).2 h
  obtain ⟨E, fieldE, hE, F, hF, hq, a, _, hirr, hnd, σ, hσ, hnon⟩ :=
    (codeNonstandard_iff_cyclicCodeWitness hn hcop).1 hc
  let : Field E := fieldE
  exact ⟨F, inferInstance, hF, hq, Concrete.rootFunctionalCode F n a,
    hirr, hnd, σ, hσ, hnon⟩

theorem functionalCodeOver_nonstandard_to_paper {F E : Type}
    [Field F] [Field E] [Finite E] [Algebra F E] {n q : ℕ}
    (hn : 0 < n) (hcop : Nat.Coprime q n) (hq : Nat.card F = q)
    (a : E) (ha : orderOf a = n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ c : Fin n → F,
      c ∈ Concrete.functionalCodeOver (F := F) (fun i : Fin n => a ^ i.val) ↔
      (c ∘ σ) ∈ Concrete.functionalCodeOver (F := F) (fun i : Fin n => a ^ i.val))
    (hnon : ¬Concrete.standardPermutation q n σ) : PaperNonstandard n q := by
  classical
  let K := (algebraMap F E).fieldRange
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = q := by
    rw [← Nat.card_congr (Concrete.coefficientEquiv (F := F) (E := E)).toEquiv]
    exact hq
  have hK' : Fintype.card K = q := by simpa only [Nat.card_eq_fintype_card] using hK
  have hperm : Concrete.preservesCode K (Concrete.rootFunctionalCode K n a) σ :=
    (Concrete.preserves_functionalCode_coefficient_image _ σ).mp hσ
  apply (codeNonstandard_iff_paper hn hcop).1
  refine ⟨E, inferInstance, inferInstance, K, inferInstance, hK, a, ha, ?_⟩
  apply (Concrete.nonstandardRootCode_iff_code_permutation K hn ha
    (hK'.symm ▸ hcop)).2
  exact ⟨σ, hperm, hK'.symm ▸ hnon⟩

#print axioms paperNonstandard_to_abstract
#print axioms functionalCodeOver_nonstandard_to_paper

end NSDensity
