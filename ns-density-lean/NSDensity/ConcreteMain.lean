import NSDensity.CodeSemantics
import NSDensity.MainReal

/-!
The density theorem for actual finite-field root-evaluation codes.  The two
external inputs are exactly the forward FHLX classification of these concrete
codes and the Wiertelak--Moree reciprocal-divergence theorem.  Descent, equality
of the prime-field and all-extension exceptional sets, and passage to ordinary
real limits are proved, rather than included in either input.
-/

namespace NSDensity

open Filter Asymptotics
open scoped Topology

/-- FHLX's forward classification, instantiated at the concrete code predicate. -/
abbrev ConcreteFHLXInput : Prop := FHLXInput CodeNonstandard

/-- All alphabets of a fixed characteristic are covered simultaneously. -/
theorem concrete_density_zero (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (ExceptionalLengths CodeNonstandard p) :=
  density_zero_fixed_characteristic hFHLX hWM hp

/-- The same set is the set of exceptional lengths over the prime alphabet. -/
theorem prime_field_density_zero (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    DensityZero (PrimeExceptionalLengths p) := by
  rw [← exceptionalLengths_eq_prime hp]
  exact concrete_density_zero hFHLX hWM hp

/-- Ordinary natural density zero for the equal prime-field exceptional set. -/
theorem prime_field_density_limit (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => (realCount (PrimeExceptionalLengths p) X : ℝ) / X)
      atTop (𝓝 0) :=
  (prime_field_density_zero hFHLX hWM hp).real_tendsto

/-- The main density problem, as a real-valued limit for arbitrary real bounds. -/
theorem concrete_density_limit (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (ExceptionalLengths CodeNonstandard p) X : ℝ) / X)
      atTop (𝓝 0) :=
  exceptional_real_proportion_tendsto_zero hFHLX hWM hp

/-- The paper's counting assertion in mathlib's standard little-o notation. -/
theorem concrete_count_isLittleO (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    (fun X : ℝ =>
      (realCount (ExceptionalLengths CodeNonstandard p) X : ℝ)) =o[atTop]
      (fun X : ℝ => X) :=
  exceptional_real_count_isLittleO hFHLX hWM hp

/-- Density one among admissible lengths, simultaneously over all extensions. -/
theorem concrete_standard_relative_density_one (hFHLX : ConcreteFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      (realCount (StandardLengths CodeNonstandard p) X : ℝ) /
        realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) :=
  standard_real_relative_proportion_tendsto_one hFHLX hWM hp

/-- Explicitly expose the quantifier over every positive alphabet exponent. -/
theorem mem_concrete_standardLengths_iff {p n : ℕ} (hn : 0 < n) :
    n ∈ StandardLengths CodeNonstandard p ↔
      Nat.Coprime p n ∧ ∀ f : ℕ, 0 < f → ¬CodeNonstandard n (p ^ f) :=
  mem_standardLengths_iff hn

#print axioms codeNonstandard_descent
#print axioms exceptionalLengths_eq_prime
#print axioms concrete_density_zero
#print axioms concrete_density_limit
#print axioms concrete_count_isLittleO
#print axioms concrete_standard_relative_density_one

end NSDensity
