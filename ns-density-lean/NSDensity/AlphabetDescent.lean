import NSDensity.PaperPairs
import Mathlib.FieldTheory.Finite.GaloisField

namespace NSDensity

/-- Every divisor of the alphabet exponent is realized by an actual subfield. -/
theorem exists_subfield_card_prime_power {E : Type*} [Field E]
    (F : Subfield E) [Finite F] {p e r : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : 0 < r) (hcard : Nat.card F = p ^ (e * r)) :
    ∃ K : Subfield E, K ≤ F ∧ Nat.card K = p ^ e := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := charP_of_card_prime_power F hp (Nat.mul_pos he hr) hcard
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Fintype F := Fintype.ofFinite F
  have hdegree : Module.finrank (ZMod p) F = e * r := by
    apply Nat.pow_right_injective hp.one_lt
    exact (FiniteField.pow_finrank_eq_natCard p F).trans hcard
  have hdiv : Module.finrank (ZMod p) (GaloisField p e) ∣
      Module.finrank (ZMod p) F := by
    rw [GaloisField.finrank p he.ne', hdegree]
    exact dvd_mul_right e r
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_iff_finrank_dvd.mpr hdiv
  let g : GaloisField p e →+* E := F.subtype.comp f.toRingHom
  refine ⟨g.fieldRange, ?_, ?_⟩
  · rintro x ⟨y, rfl⟩
    exact (f y).property
  · rw [← Nat.card_congr g.rangeRestrictFieldEquiv.toEquiv]
    exact GaloisField.card p e he.ne'

/-- Descent to any subalphabet, not only to the prime field. -/
theorem codeNonstandard_descent_exponent {p e r n : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : 0 < r) (h : CodeNonstandard n (p ^ (e * r))) :
    CodeNonstandard n (p ^ e) := by
  obtain ⟨E, fieldE, hFiniteE, F, hFiniteF, hcard, hNS⟩ := h
  let : Field E := fieldE
  let : Finite E := hFiniteE
  let : Finite F := hFiniteF
  obtain ⟨K, hKF, hK⟩ := exists_subfield_card_prime_power F hp he hr hcard
  exact ⟨E, fieldE, hFiniteE, K, inferInstance, hK,
    Concrete.nonstandardPair_of_subfield hKF hNS⟩

theorem paper_nonstandard_descent_exponent {p e r n : ℕ} (hp : p.Prime)
    (he : 0 < e) (hr : 0 < r) (hn : 0 < n) (hcop : Nat.Coprime p n)
    (h : PaperNonstandard n (p ^ (e * r))) : PaperNonstandard n (p ^ e) := by
  apply (codeNonstandard_iff_paper hn (hcop.pow_left e)).1
  exact codeNonstandard_descent_exponent hp he hr
    ((codeNonstandard_iff_paper hn (hcop.pow_left (e * r))).2 h)

#print axioms exists_subfield_card_prime_power
#print axioms paper_nonstandard_descent_exponent

end NSDensity
