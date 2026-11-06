import NSDensity.Main
import NSDensity.LittleO

/-! Real-valued quotient limits of the fixed-characteristic density theorem. -/

namespace NSDensity

open Filter
open Asymptotics
open scoped Topology

/-- The exceptional-length proportion tends to zero, with integer upper bounds. -/
theorem exceptional_proportion_tendsto_zero {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℕ => (count (ExceptionalLengths NS p) X : ℝ) / X)
      atTop (𝓝 0) :=
  (density_zero_fixed_characteristic hFHLX hWM hp).tendsto

/-- The paper's `#S_p(X) = o(X)` conclusion for arbitrary real upper bounds. -/
theorem exceptional_real_proportion_tendsto_zero {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => (realCount (ExceptionalLengths NS p) X : ℝ) / X)
      atTop (𝓝 0) :=
  (density_zero_fixed_characteristic hFHLX hWM hp).real_tendsto

/-- The main theorem in the standard little-o notation, for integer bounds. -/
theorem exceptional_count_isLittleO {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    (fun X : ℕ => (count (ExceptionalLengths NS p) X : ℝ)) =o[atTop]
      (fun X : ℕ => (X : ℝ)) :=
  (density_zero_fixed_characteristic hFHLX hWM hp).isLittleO

/-- The paper's `#S_p(X) = o(X)` in mathlib notation with a real variable. -/
theorem exceptional_real_count_isLittleO {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    (fun X : ℝ => (realCount (ExceptionalLengths NS p) X : ℝ)) =o[atTop]
      (fun X : ℝ => X) :=
  (density_zero_fixed_characteristic hFHLX hWM hp).real_isLittleO

/-- The exceptional proportion among admissible coprime lengths tends to zero. -/
theorem exceptional_relative_proportion_tendsto_zero {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℕ => (count (ExceptionalLengths NS p) X : ℝ) /
      count {n | Nat.Coprime p n} X) atTop (𝓝 0) :=
  (exceptional_relative_density_zero hFHLX hWM hp).tendsto
    ⟨1, Nat.zero_lt_one, (by simp)⟩

/-- Standard lengths have limiting proportion one among admissible lengths. -/
theorem standard_relative_proportion_tendsto_one {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℕ => (count (StandardLengths NS p) X : ℝ) /
      count {n | Nat.Coprime p n} X) atTop (𝓝 1) :=
  (standard_lengths_relative_density_one hFHLX hWM hp).tendsto
    (fun _ h => h.1) ⟨1, Nat.zero_lt_one, (by simp)⟩

/-- The same relative-density-one limit with arbitrary real upper bounds. -/
theorem standard_real_relative_proportion_tendsto_one {NS : ℕ → ℕ → Prop}
    (hFHLX : FHLXInput NS) (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ => (realCount (StandardLengths NS p) X : ℝ) /
      realCount {n | Nat.Coprime p n} X) atTop (𝓝 1) :=
  (standard_lengths_relative_density_one hFHLX hWM hp).real_tendsto
    (fun _ h => h.1) ⟨1, Nat.zero_lt_one, (by simp)⟩

#print axioms exceptional_real_proportion_tendsto_zero
#print axioms exceptional_real_count_isLittleO
#print axioms standard_real_relative_proportion_tendsto_one

end NSDensity

