import NSDensity.PaperPairs
import NSDensity.ConcreteMain

/-!
Final statements for the polynomial ideal code used in ns-density-paper.tex.
Only FHLX classification and Wiertelak--Moree are external proof parameters.
-/

namespace NSDensity

open Filter Asymptotics
open scoped Topology

abbrev PaperFHLXInput : Prop := FHLXInput PaperNonstandard

/-- The density problem for the actual polynomial-ideal code in the paper. -/
theorem paper_density_zero (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (ExceptionalLengths PaperNonstandard p) :=
  density_zero_fixed_characteristic hFHLX hWM hp

/-- The usual real density limit, with every finite alphabet of
characteristic p allowed simultaneously. -/
theorem paper_density_limit (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (ExceptionalLengths PaperNonstandard p) X : ℝ) / X)
      atTop (𝓝 0) :=
  (paper_density_zero hFHLX hWM hp).real_tendsto

/-- The paper's exact counting conclusion: number of exceptional lengths
up to X is o(X), in mathlib's standard asymptotic notation. -/
theorem paper_count_isLittleO (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    (fun X : ℝ =>
      (realCount (ExceptionalLengths PaperNonstandard p) X : ℝ)) =o[atTop]
      (fun X : ℝ => X) :=
  (paper_density_zero hFHLX hWM hp).real_isLittleO

theorem paper_prime_field_density_zero (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (PaperPrimeExceptionalLengths p) := by
  rw [← paper_exceptionalLengths_eq_prime hp]
  exact paper_density_zero hFHLX hWM hp

/-- Standard lengths have relative density one among the lengths coprime
to p, with standardness required over every positive alphabet exponent. -/
theorem paper_standard_relative_density_one (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (StandardLengths PaperNonstandard p) X : ℝ) /
        realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) :=
  standard_real_relative_proportion_tendsto_one hFHLX hWM hp

theorem paper_standard_lengths_iff {p n : ℕ} (hn : 0 < n) :
    n ∈ StandardLengths PaperNonstandard p ↔
      Nat.Coprime p n ∧ ∀ f : ℕ, 0 < f → ¬PaperNonstandard n (p ^ f) :=
  mem_standardLengths_iff hn

/-- This equivalence uses neither of the external inputs. -/
theorem paper_standard_prime_iff_all {p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hcop : Nat.Coprime p n) :
    ¬PaperNonstandard n p ↔ ∀ f : ℕ, 0 < f → ¬PaperNonstandard n (p ^ f) := by
  constructor
  · intro h f hf hNS
    exact h (paper_nonstandard_descent hp hf hn hcop hNS)
  · intro h
    simpa only [pow_one] using h 1 Nat.zero_lt_one

#print axioms paper_density_zero
#print axioms paper_density_limit
#print axioms paper_count_isLittleO
#print axioms paper_standard_relative_density_one
#print axioms paper_standard_prime_iff_all

end NSDensity
