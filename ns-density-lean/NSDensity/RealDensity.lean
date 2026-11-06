import NSDensity.Relative
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Ordinary real-valued density limits

The counting proofs use positive rational epsilon bounds.  This file identifies
those bounds with the usual real quotient limits.  No external mathematical
input is used in these bridges.
-/

namespace NSDensity

open Filter
open scoped Topology

private theorem ratio_tendsto_zero_iff (a b : ℕ → ℕ)
    (hb : ∃ N, ∀ n, N ≤ n → 0 < b n) :
    (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a n : ℚ) ≤ ε * b n) ↔
    Tendsto (fun n : ℕ => (a n : ℝ) / b n) atTop (𝓝 0) := by
  obtain ⟨Nb, hNb⟩ := hb
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro c hc
      exact Filter.Eventually.of_forall fun n =>
        lt_of_lt_of_le hc (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · intro ε hε
      obtain ⟨q, hq, hqε⟩ := exists_pos_rat_lt hε
      obtain ⟨N, hN⟩ := h q hq
      refine Filter.eventually_atTop.2 ⟨max N Nb, fun n hn => ?_⟩
      have hbound : (a n : ℝ) ≤ (q : ℝ) * b n := by
        exact_mod_cast hN n (le_trans (le_max_left _ _) hn)
      have hbpos : (0 : ℝ) < b n := by
        exact_mod_cast hNb n (le_trans (le_max_right _ _) hn)
      exact lt_of_le_of_lt ((div_le_iff₀ hbpos).2 hbound) hqε
  · intro h ε hε
    have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 ε hεreal)
    refine ⟨max N Nb, fun n hn => ?_⟩
    have hbpos : (0 : ℝ) < b n := by
      exact_mod_cast hNb n (le_trans (le_max_right _ _) hn)
    have hbound : (a n : ℝ) ≤ (ε : ℝ) * b n :=
      ((div_lt_iff₀ hbpos).1 (hN n (le_trans (le_max_left _ _) hn))).le
    exact_mod_cast hbound

/-- The rational-epsilon definition is the usual natural density zero. -/
theorem densityZero_iff_tendsto (A : Set ℕ) :
    DensityZero A ↔
      Tendsto (fun X : ℕ => (count A X : ℝ) / X) atTop (𝓝 0) := by
  exact ratio_tendsto_zero_iff (count A) id ⟨1, fun n hn => hn⟩

theorem DensityZero.tendsto {A : Set ℕ} (h : DensityZero A) :
    Tendsto (fun X : ℕ => (count A X : ℝ) / X) atTop (𝓝 0) :=
  (densityZero_iff_tendsto A).1 h

/-- A positive member of the denominator set makes its count eventually positive. -/
theorem eventually_count_pos {D : Set ℕ} (hD : ∃ n, 0 < n ∧ n ∈ D) :
    ∃ N, ∀ X, N ≤ X → 0 < count D X := by
  classical
  obtain ⟨n, hn, hnD⟩ := hD
  refine ⟨n, fun X hX => ?_⟩
  exact Finset.card_pos.2 ⟨n, Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨hn, hX⟩, hnD⟩⟩

/-- Relative density zero is convergence of the actual real quotient. -/
theorem relativeDensityZero_iff_tendsto (A D : Set ℕ)
    (hD : ∃ n, 0 < n ∧ n ∈ D) :
    RelativeDensityZero A D ↔
      Tendsto (fun X : ℕ => (count A X : ℝ) / count D X) atTop (𝓝 0) :=
  ratio_tendsto_zero_iff (count A) (count D) (eventually_count_pos hD)

theorem RelativeDensityZero.tendsto {A D : Set ℕ} (h : RelativeDensityZero A D)
    (hD : ∃ n, 0 < n ∧ n ∈ D) :
    Tendsto (fun X : ℕ => (count A X : ℝ) / count D X) atTop (𝓝 0) :=
  (relativeDensityZero_iff_tendsto A D hD).1 h

/-- For subsets, relative density one means that the real quotient tends to one. -/
theorem relativeDensityOne_iff_tendsto (G D : Set ℕ) (hGD : G ⊆ D)
    (hD : ∃ n, 0 < n ∧ n ∈ D) :
    RelativeDensityOne G D ↔
      Tendsto (fun X : ℕ => (count G X : ℝ) / count D X) atTop (𝓝 1) := by
  obtain ⟨Nb, hNb⟩ := eventually_count_pos hD
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro c hc
      obtain ⟨q, hq, hqc⟩ := exists_pos_rat_lt (sub_pos.2 hc)
      obtain ⟨N, hN⟩ := h q hq
      refine Filter.eventually_atTop.2 ⟨max N Nb, fun X hX => ?_⟩
      have hbpos : (0 : ℝ) < count D X := by
        exact_mod_cast hNb X (le_trans (le_max_right _ _) hX)
      have hbound : (1 - (q : ℝ)) * count D X ≤ count G X := by
        exact_mod_cast hN X (le_trans (le_max_left _ _) hX)
      have hcq : c < 1 - (q : ℝ) := by linarith
      exact lt_of_lt_of_le hcq ((le_div_iff₀ hbpos).2 hbound)
    · intro c hc
      refine Filter.eventually_atTop.2 ⟨Nb, fun X hX => ?_⟩
      have hbpos : (0 : ℝ) < count D X := by exact_mod_cast hNb X hX
      have hbound : (count G X : ℝ) ≤ count D X := by
        exact_mod_cast count_mono hGD X
      exact lt_of_le_of_lt ((div_le_iff₀ hbpos).2 (by simpa using hbound)) hc
  · intro h ε hε
    have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
    have hevent := (tendsto_order.1 h).1 (1 - (ε : ℝ)) (by linarith)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
    refine ⟨max N Nb, fun X hX => ?_⟩
    have hbpos : (0 : ℝ) < count D X := by
      exact_mod_cast hNb X (le_trans (le_max_right _ _) hX)
    have hbound : (1 - (ε : ℝ)) * count D X ≤ count G X :=
      ((lt_div_iff₀ hbpos).1 (hN X (le_trans (le_max_left _ _) hX))).le
    exact_mod_cast hbound

theorem RelativeDensityOne.tendsto {G D : Set ℕ} (h : RelativeDensityOne G D)
    (hGD : G ⊆ D) (hD : ∃ n, 0 < n ∧ n ∈ D) :
    Tendsto (fun X : ℕ => (count G X : ℝ) / count D X) atTop (𝓝 1) :=
  (relativeDensityOne_iff_tendsto G D hGD hD).1 h

/-- The count at a real upper bound, i.e. the count of `1 ≤ n ≤ X`. -/
noncomputable def realCount (A : Set ℕ) (X : ℝ) : ℕ := count A ⌊X⌋₊

@[simp] theorem realCount_natCast (A : Set ℕ) (X : ℕ) :
    realCount A (X : ℝ) = count A X := by
  simp [realCount]

/-- Taking the natural floor preserves divergence to positive infinity. -/
theorem natFloor_tendsto_atTop :
    Tendsto (fun X : ℝ => ⌊X⌋₊) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  refine Filter.eventually_atTop.2 ⟨(n : ℝ), fun X hX => ?_⟩
  exact (Nat.le_floor_iff (le_trans (Nat.cast_nonneg _) hX)).2 hX

/-- Density zero with arbitrary real upper bounds: precisely `#A(X) / X → 0`. -/
theorem densityZero_iff_tendsto_real (A : Set ℕ) :
    DensityZero A ↔
      Tendsto (fun X : ℝ => (realCount A X : ℝ) / X) atTop (𝓝 0) := by
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro c hc
      refine Filter.eventually_atTop.2 ⟨(1 : ℝ), fun X hX => ?_⟩
      exact lt_of_lt_of_le hc (div_nonneg (Nat.cast_nonneg _) (by linarith))
    · intro ε hε
      obtain ⟨q, hq, hqε⟩ := exists_pos_rat_lt hε
      obtain ⟨N, hN⟩ := h q hq
      refine Filter.eventually_atTop.2 ⟨max (N : ℝ) 1, fun X hX => ?_⟩
      have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one
        (le_trans (le_max_right _ _) hX)
      have hXN : (N : ℝ) ≤ X := le_trans (le_max_left _ _) hX
      have hfloor : N ≤ ⌊X⌋₊ := (Nat.le_floor_iff hXpos.le).2 hXN
      have hbound : (realCount A X : ℝ) ≤ (q : ℝ) * ⌊X⌋₊ := by
        exact_mod_cast hN ⌊X⌋₊ hfloor
      have hqnonneg : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
      have hbound' : (realCount A X : ℝ) ≤ (q : ℝ) * X :=
        hbound.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hXpos.le) hqnonneg)
      exact lt_of_le_of_lt ((div_le_iff₀ hXpos).2 hbound') hqε
  · intro h ε hε
    have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 ε hεreal)
    obtain ⟨N, hN⟩ := exists_nat_gt M
    refine ⟨max N 1, fun X hX => ?_⟩
    have hXpos : (0 : ℝ) < X := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hX)
    have hMX : M ≤ (X : ℝ) := by
      have hNX : (N : ℝ) ≤ X := by
        exact_mod_cast le_trans (le_max_left _ _) hX
      exact hN.le.trans hNX
    have hbound := hM (X : ℝ) hMX
    rw [realCount_natCast] at hbound
    have hbound' := ((div_lt_iff₀ hXpos).1 hbound).le
    exact_mod_cast hbound'

theorem DensityZero.real_tendsto {A : Set ℕ} (h : DensityZero A) :
    Tendsto (fun X : ℝ => (realCount A X : ℝ) / X) atTop (𝓝 0) :=
  (densityZero_iff_tendsto_real A).1 h

theorem RelativeDensityZero.real_tendsto {A D : Set ℕ}
    (h : RelativeDensityZero A D) (hD : ∃ n, 0 < n ∧ n ∈ D) :
    Tendsto (fun X : ℝ => (realCount A X : ℝ) / realCount D X) atTop (𝓝 0) :=
  (h.tendsto hD).comp natFloor_tendsto_atTop

theorem RelativeDensityOne.real_tendsto {G D : Set ℕ}
    (h : RelativeDensityOne G D) (hGD : G ⊆ D)
    (hD : ∃ n, 0 < n ∧ n ∈ D) :
    Tendsto (fun X : ℝ => (realCount G X : ℝ) / realCount D X) atTop (𝓝 1) :=
  (h.tendsto hGD hD).comp natFloor_tendsto_atTop

#print axioms densityZero_iff_tendsto
#print axioms densityZero_iff_tendsto_real
#print axioms relativeDensityZero_iff_tendsto
#print axioms relativeDensityOne_iff_tendsto

end NSDensity
