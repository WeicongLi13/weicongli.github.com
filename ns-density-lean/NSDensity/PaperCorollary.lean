import NSDensity.PaperMain

namespace NSDensity

open Filter
open scoped Topology

/-- The paper's ratio R_q(X). The count uses positive lengths up to the
real cutoff X. Coprimality to a prime power is equivalent to coprimality
to its characteristic. -/
noncomputable def paperRatio (q : ℕ) (X : ℝ) : ℝ :=
  (realCount (PaperPrimeExceptionalLengths q) X : ℝ) /
    realCount {n | Nat.Coprime q n} X

theorem paper_exceptional_prime_power_subset {p r : ℕ} (hp : p.Prime)
    (hr : 0 < r) :
    PaperPrimeExceptionalLengths (p ^ r) ⊆ PaperPrimeExceptionalLengths p := by
  rintro n ⟨hn, hcop, hNS⟩
  have hcop' := (Nat.coprime_pow_left_iff hr p n).1 hcop
  exact ⟨hn, hcop', paper_nonstandard_descent hp hr hn hcop' hNS⟩

/-- Every characteristic-p ratio is bounded by the prime-field ratio. -/
theorem paperRatio_prime_power_le {p r : ℕ} (hp : p.Prime)
    (hr : 0 < r) (X : ℝ) : paperRatio (p ^ r) X ≤ paperRatio p X := by
  have hcop : {n : ℕ | Nat.Coprime (p ^ r) n} = {n | Nat.Coprime p n} := by
    ext n
    exact Nat.coprime_pow_left_iff hr p n
  have hcount : realCount (PaperPrimeExceptionalLengths (p ^ r)) X ≤
      realCount (PaperPrimeExceptionalLengths p) X :=
    count_mono (paper_exceptional_prime_power_subset hp hr) _
  unfold paperRatio
  rw [hcop]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg _)

/-- The supremum in the paper is attained by the prime field, for every
real cutoff. This equality does not use either external theorem. -/
theorem paperRatio_sup_eq {p : ℕ} (hp : p.Prime) (X : ℝ) :
    (⨆ r : {r : ℕ // 0 < r}, paperRatio (p ^ (r : ℕ)) X) = paperRatio p X := by
  have : Nonempty {r : ℕ // 0 < r} := ⟨⟨1, Nat.zero_lt_one⟩⟩
  have hupper (r : {r : ℕ // 0 < r}) :
      paperRatio (p ^ (r : ℕ)) X ≤ paperRatio p X :=
    paperRatio_prime_power_le hp r.property X
  have hbdd : BddAbove (Set.range
      (fun r : {r : ℕ // 0 < r} => paperRatio (p ^ (r : ℕ)) X)) := by
    refine ⟨paperRatio p X, ?_⟩
    rintro y ⟨r, rfl⟩
    exact hupper r
  apply le_antisymm (ciSup_le hupper)
  simpa only [pow_one] using le_ciSup hbdd ⟨1, Nat.zero_lt_one⟩

theorem paperRatio_prime_tendsto_zero (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (paperRatio p) atTop (𝓝 0) := by
  exact ((paper_prime_field_density_zero hFHLX hWM hp).relative_coprime hp).real_tendsto
    ⟨1, Nat.zero_lt_one, by simp⟩

/-- The exact uniform ratio conclusion of the paper's Corollary 1.2. -/
theorem paperRatio_sup_tendsto_zero (hFHLX : PaperFHLXInput)
    (hWM : WiertelakMoreeInput) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun X : ℝ =>
      ⨆ r : {r : ℕ // 0 < r}, paperRatio (p ^ (r : ℕ)) X) atTop (𝓝 0) := by
  simpa only [paperRatio_sup_eq hp] using paperRatio_prime_tendsto_zero hFHLX hWM hp

#print axioms paperRatio_sup_eq
#print axioms paperRatio_prime_tendsto_zero
#print axioms paperRatio_sup_tendsto_zero

end NSDensity
