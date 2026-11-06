import NSDensity.AbstractRepresentation
import NSDensity.AbstractCodes
import NSDensity.FHLXPaper
import NSDensity.PaperCorollary

namespace NSDensity

open Filter Asymptotics
open scoped Topology

theorem abstractNonstandard_iff_paper {n q : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime q n) : AbstractNonstandard n q ↔ PaperNonstandard n q := by
  constructor
  · rintro ⟨F, fieldF, hF, hq, C, hirr, hnd, σ, hσ, hnon⟩
    let : Field F := fieldF
    let : Finite F := hF
    obtain ⟨E, fieldE, hE, algebraFE, a, ha, hC⟩ :=
      Concrete.irreducibleCyclicCode_exists_root_model C hirr hnd
    let : Field E := fieldE
    let : Finite E := hE
    let : Algebra F E := algebraFE
    rw [hC] at hσ
    exact functionalCodeOver_nonstandard_to_paper hn hcop hq a ha σ hσ hnon
  · exact paperNonstandard_to_abstract hn hcop

theorem abstract_exceptionalLengths_eq_paper (p : ℕ) :
    ExceptionalLengths AbstractNonstandard p = ExceptionalLengths PaperNonstandard p := by
  ext n
  constructor <;> rintro ⟨hn,hcop,f,hf,hNS⟩
  · exact ⟨hn,hcop,f,hf,(abstractNonstandard_iff_paper hn (hcop.pow_left f)).1 hNS⟩
  · exact ⟨hn,hcop,f,hf,(abstractNonstandard_iff_paper hn (hcop.pow_left f)).2 hNS⟩

/-- Density zero for arbitrary nondegenerate irreducible cyclic codes. -/
theorem abstract_density_zero (hFHLX : FHLXOriginalInput PaperNonstandard)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (ExceptionalLengths AbstractNonstandard p) := by
  rw [abstract_exceptionalLengths_eq_paper]
  exact paper_density_zero hFHLX.toFHLXInput hWM hp

theorem abstract_density_limit (hFHLX : FHLXOriginalInput PaperNonstandard)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (ExceptionalLengths AbstractNonstandard p) X : ℝ) / X)
      atTop (𝓝 0) := (abstract_density_zero hFHLX hWM hp).real_tendsto

theorem abstract_count_isLittleO (hFHLX : FHLXOriginalInput PaperNonstandard)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    (fun X : ℝ => (realCount (ExceptionalLengths AbstractNonstandard p) X : ℝ))
      =o[atTop] (fun X : ℝ => X) :=
  (abstract_density_zero hFHLX hWM hp).real_isLittleO

/-- This length set states the universal conclusion about actual code subspaces. -/
def AllCodesStandardLengths (p : ℕ) : Set ℕ :=
  {n | Nat.Coprime p n ∧ ∀ f : ℕ, 0 < f → ∀ (F : Type) (fieldF : Field F),
    letI := fieldF
    Finite F → Nat.card F = p ^ f → ∀ C : Submodule F (Fin n → F),
    Concrete.irreducibleCyclicCode C → Concrete.nondegenerateCode C →
    ∀ σ : Equiv.Perm (Fin n), (∀ c, c ∈ C ↔ (c ∘ σ) ∈ C) →
      Concrete.standardPermutation (p ^ f) n σ}

theorem allCodesStandardLengths_eq (p : ℕ) :
    AllCodesStandardLengths p = StandardLengths AbstractNonstandard p := by
  classical
  ext n
  by_cases hn : 0 < n
  · rw [mem_standardLengths_iff hn]
    simp only [AllCodesStandardLengths, Set.mem_ofPred_eq, AbstractNonstandard]
    push Not
    rfl
  · have hn0 : n = 0 := by omega
    subst n
    apply and_congr_right
    intro hcop
    constructor
    · intro _ h
      exact (Nat.lt_irrefl 0) h.1
    · intro _ f hf F fieldF hF hq C hirr hnd σ hσ
      have hzero : C = ⊥ := C.eq_bot_of_subsingleton
      exact (hirr.1 hzero).elim

theorem allCodesStandard_relative_density_one
    (hFHLX : FHLXOriginalInput PaperNonstandard) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => (realCount (AllCodesStandardLengths p) X : ℝ) /
      realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) := by
  rw [allCodesStandardLengths_eq]
  have heq : StandardLengths AbstractNonstandard p = StandardLengths PaperNonstandard p := by
    unfold StandardLengths
    rw [abstract_exceptionalLengths_eq_paper]
  rw [heq]
  exact paper_standard_relative_density_one hFHLX.toFHLXInput hWM hp

noncomputable def abstractRatio (q : ℕ) (X : ℝ) : ℝ :=
  (realCount {n | 0 < n ∧ Nat.Coprime q n ∧ AbstractNonstandard n q} X : ℝ) /
    realCount {n | Nat.Coprime q n} X

/-- The arbitrary-code ratio equals the paper's root/ideal-code ratio. -/
theorem abstractRatio_eq_paperRatio (q : ℕ) : abstractRatio q = paperRatio q := by
  have heq : {n | 0 < n ∧ Nat.Coprime q n ∧ AbstractNonstandard n q} =
      PaperPrimeExceptionalLengths q := by
    ext n
    constructor <;> rintro ⟨hn,hcop,hNS⟩
    · exact ⟨hn,hcop,(abstractNonstandard_iff_paper hn hcop).1 hNS⟩
    · exact ⟨hn,hcop,(abstractNonstandard_iff_paper hn hcop).2 hNS⟩
  funext X
  simp only [abstractRatio, paperRatio, heq]

theorem abstractRatio_sup_eq {p : ℕ} (hp : p.Prime) (X : ℝ) :
    (⨆ r : {r : ℕ // 0 < r}, abstractRatio (p ^ (r : ℕ)) X) = abstractRatio p X := by
  simp only [abstractRatio_eq_paperRatio, paperRatio_sup_eq hp]

theorem abstractRatio_sup_tendsto_zero
    (hFHLX : FHLXOriginalInput PaperNonstandard) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => ⨆ r : {r : ℕ // 0 < r},
      abstractRatio (p ^ (r : ℕ)) X) atTop (𝓝 0) := by
  simp only [abstractRatio_eq_paperRatio]
  exact paperRatio_sup_tendsto_zero hFHLX.toFHLXInput hWM hp

#print axioms abstractNonstandard_iff_paper
#print axioms abstract_density_zero
#print axioms abstract_density_limit
#print axioms abstract_count_isLittleO
#print axioms allCodesStandard_relative_density_one
#print axioms abstractRatio_sup_eq
#print axioms abstractRatio_sup_tendsto_zero

end NSDensity
