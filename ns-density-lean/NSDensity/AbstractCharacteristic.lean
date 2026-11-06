import NSDensity.AbstractMain

namespace NSDensity

open Filter Asymptotics
open scoped Topology

/-- Exceptional positive lengths for arbitrary codes over an alphabet of size q. -/
def AbstractPrimeExceptionalLengths (q : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Nat.Coprime q n ∧ AbstractNonstandard n q}

/-- Alphabet descent for arbitrary code subspaces; neither external input is used. -/
theorem abstract_nonstandard_descent {p r n : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hn : 0 < n) (hcop : Nat.Coprime p n)
    (h : AbstractNonstandard n (p ^ r)) : AbstractNonstandard n p := by
  apply (abstractNonstandard_iff_paper hn hcop).2
  exact paper_nonstandard_descent hp hr hn hcop
    ((abstractNonstandard_iff_paper hn (hcop.pow_left r)).1 h)

theorem abstract_exceptionalLengths_eq_prime {p : ℕ} (hp : p.Prime) :
    ExceptionalLengths AbstractNonstandard p = AbstractPrimeExceptionalLengths p := by
  ext n
  constructor
  · rintro ⟨hn, hcop, r, hr, hNS⟩
    exact ⟨hn, hcop, abstract_nonstandard_descent hp hr hn hcop hNS⟩
  · rintro ⟨hn, hcop, hNS⟩
    exact ⟨hn, hcop, 1, Nat.zero_lt_one, by simpa only [pow_one] using hNS⟩

/-- The literal union identity in Theorem 1.1, for arbitrary cyclic codes. -/
theorem abstract_prime_power_union_eq_prime {p : ℕ} (hp : p.Prime) :
    (⋃ r : {r : ℕ // 0 < r}, AbstractPrimeExceptionalLengths (p ^ (r : ℕ))) =
      AbstractPrimeExceptionalLengths p := by
  apply Set.Subset.antisymm
  · intro n hn
    obtain ⟨r, hn, hcop, hNS⟩ := Set.mem_iUnion.mp hn
    have hcop' := (Nat.coprime_pow_left_iff r.property p n).1 hcop
    exact ⟨hn, hcop', abstract_nonstandard_descent hp r.property hn hcop' hNS⟩
  · intro n hn
    apply Set.mem_iUnion.mpr
    exact ⟨⟨1, Nat.zero_lt_one⟩, by simpa only [pow_one] using hn⟩

/-- A good length controls every actual finite field of characteristic p,
without requiring the user to supply its cardinality exponent. -/
theorem allCodesStandardLengths_charP {p n : ℕ} (hn : n ∈ AllCodesStandardLengths p)
    (F : Type) [Field F] [Finite F] [CharP F p]
    (C : Submodule F (Fin n → F)) (hirr : Concrete.irreducibleCyclicCode C)
    (hnd : Concrete.nondegenerateCode C) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ c, c ∈ C ↔ (c ∘ σ) ∈ C) :
    Concrete.standardPermutation (Nat.card F) n σ := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨r, _, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (r : ℕ) := by simpa using hcard
  rw [hcard']
  exact hn.2 r.val r.property F inferInstance inferInstance hcard' C hirr hnd σ hσ

/-- The paper's universal conclusion, phrased directly using characteristic. -/
def CharacteristicStandardLengths (p : ℕ) : Set ℕ :=
  {n | Nat.Coprime p n ∧ ∀ (F : Type) (fieldF : Field F),
    letI := fieldF
    Finite F → CharP F p → ∀ C : Submodule F (Fin n → F),
      Concrete.irreducibleCyclicCode C → Concrete.nondegenerateCode C →
      ∀ σ : Equiv.Perm (Fin n), (∀ c, c ∈ C ↔ (c ∘ σ) ∈ C) →
        Concrete.standardPermutation (Nat.card F) n σ}

theorem characteristicStandardLengths_eq {p : ℕ} (hp : p.Prime) :
    CharacteristicStandardLengths p = AllCodesStandardLengths p := by
  ext n
  constructor
  · rintro ⟨hcop, hstd⟩
    refine ⟨hcop, ?_⟩
    intro r hr F fieldF hF hcard C hirr hnd σ hσ
    let : Field F := fieldF
    let : Finite F := hF
    have hchar : CharP F p := charP_of_card_prime_power F hp hr hcard
    rw [← hcard]
    exact hstd F fieldF hF hchar C hirr hnd σ hσ
  · intro h
    refine ⟨h.1, ?_⟩
    intro F fieldF hF hchar C hirr hnd σ hσ
    let : Field F := fieldF
    let : Finite F := hF
    let : CharP F p := hchar
    exact allCodesStandardLengths_charP h F C hirr hnd σ hσ

theorem characteristic_standard_relative_density_one
    (hFHLX : FHLXOriginalInput PaperNonstandard) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => (realCount (CharacteristicStandardLengths p) X : ℝ) /
      realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) := by
  rw [characteristicStandardLengths_eq hp]
  exact allCodesStandard_relative_density_one hFHLX hWM hp

/-- Theorem 1.1 for arbitrary code subspaces, including its direct
characteristic-p interpretation. -/
theorem abstract_density_main
    (hFHLX : FHLXOriginalInput PaperNonstandard) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    (⋃ r : {r : ℕ // 0 < r}, AbstractPrimeExceptionalLengths (p ^ (r : ℕ))) =
        AbstractPrimeExceptionalLengths p ∧
      (fun X : ℝ => (realCount (AbstractPrimeExceptionalLengths p) X : ℝ))
        =o[atTop] (fun X : ℝ => X) ∧
      Tendsto (fun X : ℝ => (realCount (CharacteristicStandardLengths p) X : ℝ) /
        realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) := by
  refine ⟨abstract_prime_power_union_eq_prime hp, ?_,
    characteristic_standard_relative_density_one hFHLX hWM hp⟩
  rw [← abstract_exceptionalLengths_eq_prime hp]
  exact abstract_count_isLittleO hFHLX hWM hp

#print axioms abstract_nonstandard_descent
#print axioms abstract_prime_power_union_eq_prime
#print axioms allCodesStandardLengths_charP
#print axioms characteristicStandardLengths_eq
#print axioms characteristic_standard_relative_density_one
#print axioms abstract_density_main

end NSDensity
