import NSDensity.RealDensity
import Mathlib.Analysis.Asymptotics.Defs

/-! The standard mathlib little-o notation for the density-zero conclusion. -/

namespace NSDensity

open Filter Asymptotics
open scoped Topology

/-- The rational-epsilon counting definition is exactly the standard `o(X)`. -/
theorem densityZero_iff_isLittleO (A : Set ℕ) :
    DensityZero A ↔
      (fun X : ℕ => (count A X : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  constructor
  · intro h
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨q, hq, hqε⟩ := exists_pos_rat_lt hε
    obtain ⟨N, hN⟩ := h q hq
    refine Filter.eventually_atTop.2 ⟨N, fun X hX => ?_⟩
    have hbound : (count A X : ℝ) ≤ (q : ℝ) * X := by
      exact_mod_cast hN X hX
    have hbound' : (count A X : ℝ) ≤ ε * X :=
      hbound.trans (mul_le_mul_of_nonneg_right hqε.le (Nat.cast_nonneg _))
    simpa only [Real.norm_natCast] using hbound'
  · intro h ε hε
    have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.bound hεreal)
    refine ⟨N, fun X hX => ?_⟩
    have hbound : (count A X : ℝ) ≤ (ε : ℝ) * X := by
      simpa only [Real.norm_natCast] using hN X hX
    exact_mod_cast hbound

theorem DensityZero.isLittleO {A : Set ℕ} (h : DensityZero A) :
    (fun X : ℕ => (count A X : ℝ)) =o[atTop] (fun X : ℕ => (X : ℝ)) :=
  (densityZero_iff_isLittleO A).1 h

/-- The same `o(X)` statement for the real-variable counting function. -/
theorem densityZero_iff_isLittleO_real (A : Set ℕ) :
    DensityZero A ↔
      (fun X : ℝ => (realCount A X : ℝ)) =o[atTop] (fun X : ℝ => X) := by
  constructor
  · intro h
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have hevent := (tendsto_order.1 h.real_tendsto).2 ε hε
    apply (hevent.and (Filter.eventually_ge_atTop (1 : ℝ))).mono
    rintro X ⟨hbound, hX⟩
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hbound' : (realCount A X : ℝ) ≤ ε * X :=
      ((div_lt_iff₀ hXpos).1 hbound).le
    simpa only [Real.norm_natCast,
      Real.norm_of_nonneg hXpos.le] using hbound'
  · intro h
    apply (densityZero_iff_tendsto_real A).2
    apply tendsto_order.2
    constructor
    · intro c hc
      apply (Filter.eventually_ge_atTop (1 : ℝ)).mono
      intro X hX
      exact lt_of_lt_of_le hc (div_nonneg (Nat.cast_nonneg _) (by linarith))
    · intro ε hε
      have hevent := h.bound (show 0 < ε / 2 by positivity)
      apply (hevent.and (Filter.eventually_ge_atTop (1 : ℝ))).mono
      rintro X ⟨hbound, hX⟩
      have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
      have hbound' : (realCount A X : ℝ) ≤ ε / 2 * X := by
        simpa only [Real.norm_natCast,
          Real.norm_of_nonneg hXpos.le] using hbound
      exact lt_of_le_of_lt ((div_le_iff₀ hXpos).2 hbound') (by linarith)

theorem DensityZero.real_isLittleO {A : Set ℕ} (h : DensityZero A) :
    (fun X : ℝ => (realCount A X : ℝ)) =o[atTop] (fun X : ℝ => X) :=
  (densityZero_iff_isLittleO_real A).1 h

#print axioms densityZero_iff_isLittleO
#print axioms densityZero_iff_isLittleO_real

end NSDensity


