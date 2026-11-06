import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
The elementary counting foundation for the density argument.
This file introduces no external mathematical assumptions.
The counting interval is exactly {1, ..., X}.
-/

namespace NSDensity

noncomputable def count (A : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => n ∈ A)).card

/-- Natural density zero, stated with positive rational epsilon bounds. -/
def DensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (count A X : ℚ) ≤ ε * X

theorem count_mono {A B : Set ℕ} (h : A ⊆ B) (X : ℕ) : count A X ≤ count B X := by
  classical
  unfold count
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnX, hnA⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnX, h hnA⟩

@[simp] theorem count_empty (X : ℕ) : count ∅ X = 0 := by
  classical
  simp [count]

theorem count_union_le (A B : Set ℕ) (X : ℕ) :
    count (A ∪ B) X ≤ count A X + count B X := by
  classical
  unfold count
  simp only [Set.mem_union, Finset.filter_or]
  exact Finset.card_union_le _ _

theorem DensityZero.mono {A B : Set ℕ} (hB : DensityZero B) (h : A ⊆ B) :
    DensityZero A := by
  intro ε hε
  obtain ⟨N, hN⟩ := hB ε hε
  refine ⟨N, fun X hX => le_trans ?_ (hN X hX)⟩
  exact_mod_cast count_mono h X

@[simp] theorem densityZero_empty : DensityZero ∅ := by
  intro ε hε
  refine ⟨0, fun X _ => ?_⟩
  simp only [count_empty, Nat.cast_zero]
  positivity

theorem DensityZero.union {A B : Set ℕ} (hA : DensityZero A) (hB : DensityZero B) :
    DensityZero (A ∪ B) := by
  intro ε hε
  obtain ⟨NA, hNA⟩ := hA (ε / 2) (by positivity)
  obtain ⟨NB, hNB⟩ := hB (ε / 2) (by positivity)
  refine ⟨max NA NB, fun X hX => ?_⟩
  have hAX := hNA X (le_trans (le_max_left _ _) hX)
  have hBX := hNB X (le_trans (le_max_right _ _) hX)
  have hcount : (count (A ∪ B) X : ℚ) ≤ count A X + count B X := by
    exact_mod_cast count_union_le A B X
  linarith

theorem count_multiples (a X : ℕ) : count {n : ℕ | a ∣ n} X = X / a := by
  classical
  have hinterval : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simpa only [count, Set.mem_ofPred_eq, hinterval] using
    Nat.Ioc_filter_dvd_card_eq_div X a

theorem count_le_div_of_subset_multiples {A : Set ℕ} {a : ℕ}
    (hA : A ⊆ {n : ℕ | a ∣ n}) (X : ℕ) : count A X ≤ X / a := by
  simpa only [count_multiples] using count_mono hA X

theorem DensityZero.biUnion_finset {ι : Type*} (s : Finset ι) (A : ι → Set ℕ)
    (h : ∀ i ∈ s, DensityZero (A i)) : DensityZero (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsingle := h i (Finset.mem_insert_self i s)
    have hrest : DensityZero (⋃ j ∈ s, A j) :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa using hsingle.union hrest

theorem count_biUnion_finset_le {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) (X : ℕ) :
    count (⋃ i ∈ s, A i) X ≤ ∑ i ∈ s, count (A i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    calc
      count (⋃ j ∈ insert i s, A j) X = count (A i ∪ ⋃ j ∈ s, A j) X := by simp
      _ ≤ count (A i) X + count (⋃ j ∈ s, A j) X := count_union_le _ _ _
      _ ≤ count (A i) X + ∑ j ∈ s, count (A j) X := Nat.add_le_add_left ih _
      _ = ∑ j ∈ insert i s, count (A j) X := by simp [hi]

/-- A uniform additive counting error does not affect density zero. -/
theorem densityZero_of_count_bound {A : Set ℕ}
    (h : ∀ ε : ℚ, 0 < ε → ∃ C : ℚ, ∀ X : ℕ,
      (count A X : ℚ) ≤ ε * X + C) : DensityZero A := by
  intro ε hε
  obtain ⟨C, hC⟩ := h (ε / 2) (by positivity)
  let N := (2 * C / ε).ceil.toNat + 1
  have hceil : 2 * C / ε ≤ (((2 * C / ε).ceil.toNat : ℕ) : ℚ) := by
    apply le_trans Rat.le_ceil
    exact_mod_cast Int.self_le_toNat (2 * C / ε).ceil
  have hN : 2 * C / ε < (N : ℚ) := by
    dsimp [N]
    push_cast
    linarith
  refine ⟨N, fun X hX => ?_⟩
  have hNX : (N : ℚ) ≤ X := by exact_mod_cast hX
  have hlarge : 2 * C / ε < (X : ℚ) := lt_of_lt_of_le hN hNX
  have hCsmall : 2 * C < (X : ℚ) * ε := (div_lt_iff₀ hε).mp hlarge
  have hbound := hC X
  nlinarith

/-- Approximation by a zero-density set, with arbitrarily small linear error. -/
theorem densityZero_of_approximation {A : Set ℕ}
    (h : ∀ ε : ℚ, 0 < ε → ∃ B : Set ℕ, DensityZero B ∧
      ∀ X : ℕ, (count A X : ℚ) ≤ count B X + ε * X) : DensityZero A := by
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := h (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := hB (ε / 2) (by positivity)
  refine ⟨N, fun X hX => ?_⟩
  have hBX := hN X hX
  have hAX := hAB X
  linarith

#print axioms densityZero_of_approximation
#print axioms densityZero_of_count_bound

end NSDensity
