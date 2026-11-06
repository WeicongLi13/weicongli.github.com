import NSDensity.CodeModelGenerated
import NSDensity.ConcreteIrreducible
import NSDensity.CodePolynomial
import NSDensity.ConcretePairs

/-!
Identification of the concrete exceptional-pair predicate with a coordinate
permutation of the actual generator-matrix cyclic code lying outside the
standard shift/Frobenius group.  In particular, non-affineness is not an extra
coding-theoretic assumption: its equivalence with nonstandardness is proved.
-/

namespace NSDensity.Concrete

variable {E : Type*} [Field E] [Finite E]

/-- Nonstandardness expressed directly on the code, with the usual standard
shift/Frobenius permutations and the usual preservation of codewords. -/
theorem nonstandardRootCode_iff_code_permutation (F : Subfield E) [Fintype F]
    {a : E} {n : ℕ} (hn : 0 < n) (ha : orderOf a = n)
    (hcop : Nat.Coprime (Fintype.card F) n) :
    nonstandardRootCode F n a ↔
      ∃ σ : Equiv.Perm (Fin n),
        preservesCode F (rootFunctionalCode F n a) σ ∧
          ¬standardPermutation (Fintype.card F) n σ := by
  rw [nonstandardRootCode_iff_outside_standard F hn ha hcop]
  apply exists_congr
  intro σ
  exact and_congr_left fun _ =>
    preservesRelations_iff_preserves_functionalCode_general F _ σ

end NSDensity.Concrete

namespace NSDensity

/-- A concrete finite-field witness, written using the code's actual
permutation automorphisms rather than its dual relation kernel. -/
def NonstandardCyclicCodeWitness (E : Type) [Field E] (n q : ℕ) : Prop :=
  Finite E ∧ ∃ F : Subfield E, Finite F ∧ Nat.card F = q ∧
    ∃ a : E, orderOf a = n ∧
      Concrete.irreducibleCyclicCode (Concrete.rootFunctionalCode F n a) ∧
      Concrete.nondegenerateCode (Concrete.rootFunctionalCode F n a) ∧
      ∃ σ : Equiv.Perm (Fin n),
      Concrete.preservesCode F (Concrete.rootFunctionalCode F n a) σ ∧
        ¬Concrete.standardPermutation q n σ

/-- The exceptional-pair predicate has a fully expanded finite-field,
codeword, and permutation interpretation. -/
theorem codeNonstandard_iff_cyclicCodeWitness {n q : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime q n) :
    CodeNonstandard n q ↔
      ∃ (E : Type) (fieldE : Field E),
        @NonstandardCyclicCodeWitness E fieldE n q := by
  constructor
  · rintro ⟨E, fieldE, hE, F, hF, hq, a, ha, hNS⟩
    let : Field E := fieldE
    let : Finite E := hE
    let : Finite F := hF
    let := Fintype.ofFinite F
    have hcard : Fintype.card F = q := by simpa only [Nat.card_eq_fintype_card] using hq
    have hcop' : Nat.Coprime (Fintype.card F) n := hcard.symm ▸ hcop
    obtain ⟨σ, hσ, hnon⟩ :=
      (Concrete.nonstandardRootCode_iff_code_permutation F hn ha hcop').1 hNS
    obtain ⟨hirred, hnd⟩ :=
      Concrete.rootFunctionalCode_is_nondegenerate_irreducible F hn a ha
    exact ⟨E, fieldE, hE, F, hF, hq, a, ha, hirred, hnd, σ, hσ, hcard ▸ hnon⟩
  · rintro ⟨E, fieldE, hE, F, hF, hq, a, ha, _, _, σ, hσ, hnon⟩
    let : Field E := fieldE
    let : Finite E := hE
    let : Finite F := hF
    let := Fintype.ofFinite F
    have hcard : Fintype.card F = q := by simpa only [Nat.card_eq_fintype_card] using hq
    have hcop' : Nat.Coprime (Fintype.card F) n := hcard.symm ▸ hcop
    refine ⟨E, fieldE, hE, F, hF, hq, a, ha, ?_⟩
    exact (Concrete.nonstandardRootCode_iff_code_permutation F hn ha hcop').2
      ⟨σ, hσ, hcard.symm ▸ hnon⟩

#print axioms Concrete.nonstandardRootCode_iff_code_permutation
#print axioms codeNonstandard_iff_cyclicCodeWitness

end NSDensity
