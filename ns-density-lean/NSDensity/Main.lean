import NSDensity.Cover
import NSDensity.ESDensity
import NSDensity.Relative

/-!
The fixed-characteristic density theorem, relative only to the two external
theorems explicitly accepted by the user. Both are ordinary proof parameters.
All construction reductions, arithmetic, sieving, infinite-union estimates,
and coverage of the five initial families are proved in the imported files.
-/

namespace NSDensity

/-- For every fixed prime p, the lengths nonstandard over at least one finite
field of characteristic p have natural density zero. -/
theorem density_zero_fixed_characteristic {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) : DensityZero (ExceptionalLengths NS p) := by
  have hOther := densityZero_otherLengths hWM hp.one_lt
  have hES := densityZero_equallySpaced hWM hp.one_lt
  exact (hOther.union hES).mono (exceptionalLengths_subset hFHLX hp)

/-- The explicit epsilon-counting form of the main result, for all positive
rational epsilon and all sufficiently large integer bounds X. -/
theorem exceptional_count_le {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) {ε : ℚ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (count (ExceptionalLengths NS p) X : ℚ) ≤ ε * X :=
  density_zero_fixed_characteristic hFHLX hWM hp ε hε

/-- The conclusion at any one fixed positive alphabet exponent. -/
theorem density_zero_fixed_alphabet {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    DensityZero {n | 0 < n ∧ Nat.Coprime p n ∧ NS n (p ^ r)} := by
  apply (density_zero_fixed_characteristic hFHLX hWM hp).mono
  rintro n ⟨hn, hcop, hNS⟩
  exact ⟨hn, hcop, r, hr, hNS⟩

def StandardLengths (NS : ℕ → ℕ → Prop) (p : ℕ) : Set ℕ :=
  {n | Nat.Coprime p n} \ ExceptionalLengths NS p

/-- On positive lengths the complement means standard over every positive
alphabet exponent, with the quantifier in the simultaneous order. -/
theorem mem_standardLengths_iff {NS : ℕ → ℕ → Prop} {p n : ℕ} (hn : 0 < n) :
    n ∈ StandardLengths NS p ↔
      Nat.Coprime p n ∧ ∀ f : ℕ, 0 < f → ¬NS n (p ^ f) := by
  constructor
  · rintro ⟨hcop, hexc⟩
    exact ⟨hcop, fun f hf hNS => hexc ⟨hn, hcop, f, hf, hNS⟩⟩
  · rintro ⟨hcop, hstd⟩
    refine ⟨hcop, ?_⟩
    rintro ⟨_, _, f, hf, hNS⟩
    exact hstd f hf hNS

theorem exceptional_relative_density_zero {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    RelativeDensityZero (ExceptionalLengths NS p) {n | Nat.Coprime p n} :=
  (density_zero_fixed_characteristic hFHLX hWM hp).relative_coprime hp

theorem standard_lengths_relative_density_one {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    RelativeDensityOne (StandardLengths NS p) {n | Nat.Coprime p n} := by
  apply (exceptional_relative_density_zero hFHLX hWM hp).compl
  intro n hn
  exact hn.2.1

#print axioms density_zero_fixed_characteristic
#print axioms exceptional_count_le
#print axioms standard_lengths_relative_density_one

end NSDensity
