import NSDensity.FHLXOriginal
import NSDensity.AlphabetDescent
import NSDensity.PaperMain

/-!
The density paper, with the original FHLX hypotheses at its boundary.

`PaperOriginalFHLXInput` records the original classification, its five
nonstandard initial families, and the four constructions stated in FHLX.
General alphabet descent is proved internally in `AlphabetDescent`.
The analytic density conclusions additionally use `WiertelakMoreeInput`.
-/

namespace NSDensity

open Filter Asymptotics
open scoped Topology

abbrev PaperOriginalFHLXInput : Prop := FHLXOriginalInput PaperNonstandard

/-- Unrestricted descent is an internal theorem about the actual paper code. -/
theorem paper_unrestrictedDescentRule : UnrestrictedDescentRule PaperNonstandard := by
  intro p hp n e r hn hcop he hr hNS
  exact paper_nonstandard_descent_exponent hp he hr hn hcop hNS

/-- Classification by exactly the initial families and four constructions
in the original FHLX statement. -/
theorem paper_original_nonstandard_iff_originalDerived
    (hFHLX : PaperOriginalFHLXInput) {p n f : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hcop : Nat.Coprime p n) (hf : 0 < f) :
    PaperNonstandard n (p ^ f) ↔ ∃ a e : ℕ, FHLXInitial p a e ∧
      FHLXDerived p (a, e) (n, f) :=
  hFHLX.nonstandard_iff_originalDerived hp hn hcop hf

/-- The elementary closure used in the density paper is equivalent to
nonstandardness; no extra initial cases are assumed nonstandard. -/
theorem paper_original_nonstandard_iff_derived
    (hFHLX : PaperOriginalFHLXInput) {p n f : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hcop : Nat.Coprime p n) (hf : 0 < f) :
    PaperNonstandard n (p ^ f) ↔ ∃ a e : ℕ, FHLXInitial p a e ∧
      Derived p (a, e) (n, f) :=
  hFHLX.nonstandard_iff_derived paper_unrestrictedDescentRule hp hn hcop hf

/-- An exact normal-form characterization of the paper's nonstandard pairs. -/
theorem paper_original_nonstandard_iff_normalForm
    (hFHLX : PaperOriginalFHLXInput) {p n f : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hcop : Nat.Coprime p n) (hf : 0 < f) :
    PaperNonstandard n (p ^ f) ↔ ∃ a e : ℕ, FHLXInitial p a e ∧
      NormalForm p (a, e) (n, f) := by
  rw [paper_original_nonstandard_iff_derived hFHLX hp hn hcop hf]
  constructor
  · rintro ⟨a, e, hinit, hpath⟩
    exact ⟨a, e, hinit, derived_normalForm hp.one_lt.le hinit.1 hpath⟩
  · rintro ⟨a, e, hinit, hnormal⟩
    exact ⟨a, e, hinit, normalForm_derived hinit.1 hinit.2.1 hnormal⟩

/-- Density zero follows from the actual original FHLX input and WM. -/
theorem paper_original_density_zero (hFHLX : PaperOriginalFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (ExceptionalLengths PaperNonstandard p) :=
  paper_density_zero hFHLX.toFHLXInput hWM hp

theorem paper_original_density_limit (hFHLX : PaperOriginalFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (ExceptionalLengths PaperNonstandard p) X : ℝ) / X)
      atTop (𝓝 0) :=
  paper_density_limit hFHLX.toFHLXInput hWM hp

theorem paper_original_count_isLittleO (hFHLX : PaperOriginalFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    (fun X : ℝ =>
      (realCount (ExceptionalLengths PaperNonstandard p) X : ℝ)) =o[atTop]
      (fun X : ℝ => X) :=
  paper_count_isLittleO hFHLX.toFHLXInput hWM hp

theorem paper_original_prime_field_density_zero (hFHLX : PaperOriginalFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (PaperPrimeExceptionalLengths p) :=
  paper_prime_field_density_zero hFHLX.toFHLXInput hWM hp

/-- The main theorem's equality of exceptional sets and counting conclusion. -/
theorem paper_original_density_main (hFHLX : PaperOriginalFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    ExceptionalLengths PaperNonstandard p = PaperPrimeExceptionalLengths p ∧
      (fun X : ℝ => (realCount (PaperPrimeExceptionalLengths p) X : ℝ)) =o[atTop]
        (fun X : ℝ => X) :=
  ⟨paper_exceptionalLengths_eq_prime hp,
    (paper_original_prime_field_density_zero hFHLX hWM hp).real_isLittleO⟩

theorem paper_original_standard_relative_density_one
    (hFHLX : PaperOriginalFHLXInput) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (StandardLengths PaperNonstandard p) X : ℝ) /
        realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) :=
  paper_standard_relative_density_one hFHLX.toFHLXInput hWM hp

#print axioms paper_unrestrictedDescentRule
#print axioms paper_original_nonstandard_iff_normalForm
#print axioms paper_original_density_main
#print axioms paper_original_standard_relative_density_one

end NSDensity
