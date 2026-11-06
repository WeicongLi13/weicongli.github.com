import NSDensity.CodeSemantics
import NSDensity.CodeIdeal

/-!
The pair predicate expressed using exactly the polynomial ideal displayed in
the paper, rather than a chosen generator matrix or its relation kernel.
The equivalence below proves the change of models, including the inverse root.
-/

namespace NSDensity

def PaperNonstandardOver (E : Type) [Field E] (n q : ℕ) : Prop :=
  Finite E ∧ ∃ F : Subfield E, Finite F ∧ Nat.card F = q ∧
    ∃ a : E, orderOf a = n ∧ ∃ σ : Equiv.Perm (Fin n),
      Concrete.preservesCode F (Concrete.polynomialCyclicCode F n a) σ ∧
        ¬Concrete.standardPermutation q n σ

/-- Nonstandardness of the paper's actual ideal code, using coefficient words. -/
def PaperNonstandard (n q : ℕ) : Prop :=
  ∃ (E : Type) (fieldE : Field E), @PaperNonstandardOver E fieldE n q

theorem codeNonstandard_iff_paper {n q : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime q n) : CodeNonstandard n q ↔ PaperNonstandard n q := by
  rw [codeNonstandard_iff_cyclicCodeWitness hn hcop]
  constructor
  · rintro ⟨E, fieldE, hE, F, hF, hq, a, ha, _, _, σ, hσ, hnon⟩
    let : Field E := fieldE
    let : Finite E := hE
    have hainv : orderOf a⁻¹ = n := (Concrete.inverse_root_orderOf a).trans ha
    have hcode := Concrete.polynomialCyclicCode_eq_rootFunctionalCode F hn a⁻¹ hainv
    simp only [inv_inv] at hcode
    refine ⟨E, fieldE, hE, F, hF, hq, a⁻¹, hainv, σ, ?_, hnon⟩
    simpa only [hcode] using hσ
  · rintro ⟨E, fieldE, hE, F, hF, hq, a, ha, σ, hσ, hnon⟩
    let : Field E := fieldE
    let : Finite E := hE
    have hainv : orderOf a⁻¹ = n := (Concrete.inverse_root_orderOf a).trans ha
    have hcode := Concrete.polynomialCyclicCode_eq_rootFunctionalCode F hn a ha
    obtain ⟨hirred, hnd⟩ :=
      Concrete.rootFunctionalCode_is_nondegenerate_irreducible F hn a⁻¹ hainv
    exact ⟨E, fieldE, hE, F, hF, hq, a⁻¹, hainv, hirred, hnd, σ,
      by simpa only [hcode] using hσ, hnon⟩

theorem paper_nonstandard_descent {p r n : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hn : 0 < n) (hcop : Nat.Coprime p n)
    (h : PaperNonstandard n (p ^ r)) : PaperNonstandard n p := by
  apply (codeNonstandard_iff_paper hn hcop).1
  apply codeNonstandard_descent hp hr
  exact (codeNonstandard_iff_paper hn (hcop.pow_left r)).2 h

def PaperPrimeExceptionalLengths (p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Nat.Coprime p n ∧ PaperNonstandard n p}

theorem paper_exceptionalLengths_eq_prime {p : ℕ} (hp : p.Prime) :
    ExceptionalLengths PaperNonstandard p = PaperPrimeExceptionalLengths p := by
  ext n
  constructor
  · rintro ⟨hn, hcop, r, hr, hNS⟩
    exact ⟨hn, hcop, paper_nonstandard_descent hp hr hn hcop hNS⟩
  · rintro ⟨hn, hcop, hNS⟩
    exact ⟨hn, hcop, 1, by decide, by simpa only [pow_one] using hNS⟩

theorem paper_exceptionalLengths_eq_concrete (p : ℕ) :
    ExceptionalLengths PaperNonstandard p = ExceptionalLengths CodeNonstandard p := by
  ext n
  constructor <;> rintro ⟨hn, hcop, f, hf, hNS⟩
  · exact ⟨hn, hcop, f, hf, (codeNonstandard_iff_paper hn (hcop.pow_left f)).2 hNS⟩
  · exact ⟨hn, hcop, f, hf, (codeNonstandard_iff_paper hn (hcop.pow_left f)).1 hNS⟩

/-- Changing code models changes no part of the permitted classification input. -/
theorem paperFHLX_to_concrete (hFHLX : FHLXInput PaperNonstandard) :
    FHLXInput CodeNonstandard := by
  intro p hp n f hn hcop hf hNS
  exact hFHLX p hp n f hn hcop hf
    ((codeNonstandard_iff_paper hn (hcop.pow_left f)).1 hNS)

#print axioms codeNonstandard_iff_paper
#print axioms paper_nonstandard_descent
#print axioms paper_exceptionalLengths_eq_prime

end NSDensity
