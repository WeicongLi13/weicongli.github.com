import NSDensity.Basic

/-! Relative density among lengths coprime to a fixed prime. -/

namespace NSDensity

def RelativeDensityZero (A D : Set ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (count A X : ℚ) ≤ ε * count D X

def RelativeDensityOne (G D : Set ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (1 - ε) * (count D X : ℚ) ≤ count G X

/-- Prime multiples and coprime lengths partition the positive counting interval. -/
theorem count_coprime_add_count_multiples {p : ℕ} (hp : p.Prime) (X : ℕ) :
    count {n : ℕ | Nat.Coprime p n} X + count {n : ℕ | p ∣ n} X = X := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 X) (fun n : ℕ => p ∣ n)
  simpa [count, hp.coprime_iff_not_dvd, Nat.add_comm] using h

/-- At least half of the positive integers are coprime to any fixed prime. -/
theorem count_coprime_lower_bound {p : ℕ} (hp : p.Prime) (X : ℕ) :
    (X : ℚ) ≤ 2 * count {n : ℕ | Nat.Coprime p n} X := by
  have hpart := count_coprime_add_count_multiples hp X
  rw [count_multiples] at hpart
  have hmul : X / p * 2 ≤ X :=
    (Nat.mul_le_mul_left (X / p) hp.two_le).trans (Nat.div_mul_le_self X p)
  have hbound : X ≤ 2 * count {n : ℕ | Nat.Coprime p n} X := by omega
  exact_mod_cast hbound

/-- Absolute density zero implies relative density zero among lengths coprime to p. -/
theorem DensityZero.relative_coprime {A : Set ℕ} (hA : DensityZero A)
    {p : ℕ} (hp : p.Prime) :
    RelativeDensityZero A {n : ℕ | Nat.Coprime p n} := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA (ε / 2) (by positivity)
  refine ⟨N, fun X hX => ?_⟩
  have hcount := hN X hX
  have hbound := count_coprime_lower_bound hp X
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ ε / 2 by positivity)
  nlinarith

/-- Removing a subset splits the finite count exactly. -/
theorem count_diff_add_count_of_subset {A D : Set ℕ} (hAD : A ⊆ D) (X : ℕ) :
    count (D \ A) X + count A X = count D X := by
  classical
  have hsub : (Finset.Icc 1 X).filter (fun n => n ∈ A) ⊆
      (Finset.Icc 1 X).filter (fun n => n ∈ D) := by
    intro n hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnI, hAD hnA⟩
  have hdiff : ((Finset.Icc 1 X).filter (fun n => n ∈ D)) \
      ((Finset.Icc 1 X).filter (fun n => n ∈ A)) =
      (Finset.Icc 1 X).filter (fun n => n ∈ D \ A) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_filter, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨hnI, hnD⟩, hnot⟩
      exact ⟨hnI, hnD, fun hnA => hnot ⟨hnI, hnA⟩⟩
    · rintro ⟨hnI, hnD, hnA⟩
      exact ⟨⟨hnI, hnD⟩, fun ⟨_, hnA'⟩ => hnA hnA'⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff] at hcard
  convert hcard using 1 <;> simp only [count]
  congr 2
  ext n
  simp

/-- A subset of relative density zero leaves a relative-density-one complement. -/
theorem RelativeDensityZero.compl {A D : Set ℕ} (h : RelativeDensityZero A D)
    (hAD : A ⊆ D) : RelativeDensityOne (D \ A) D := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun X hX => ?_⟩
  have hcount := hN X hX
  have hpart : (count (D \ A) X : ℚ) + count A X = count D X := by
    exact_mod_cast count_diff_add_count_of_subset hAD X
  nlinarith

end NSDensity
