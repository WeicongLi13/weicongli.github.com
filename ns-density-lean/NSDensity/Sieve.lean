import NSDensity.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
The elementary prime sieve used in the density paper. The reciprocal divergence
hypothesis is expressed by unbounded finite sums over positive rationals.
There are no external theorem assumptions in this module.
-/

namespace NSDensity

def reciprocalMass (F : Finset ℕ) : ℚ := ∑ p ∈ F, (p : ℚ)⁻¹

def sieveWeight (F : Finset ℕ) : ℚ := ∏ p ∈ F, (1 - (p : ℚ)⁻¹)

/-- Divergence of the reciprocal sum, expressed by unbounded finite subsums. -/
def ReciprocalDiverges (P : Set ℕ) : Prop :=
  ∀ C : ℚ, ∃ F : Finset ℕ, (∀ p ∈ F, p ∈ P) ∧ C < reciprocalMass F

theorem reciprocalMass_nonneg (F : Finset ℕ) : 0 ≤ reciprocalMass F := by
  unfold reciprocalMass
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem sieveWeight_nonneg {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    0 ≤ sieveWeight F := by
  unfold sieveWeight
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast (hF p hp).one_lt.le
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (hF p hp).pos
  have := (inv_le_one₀ hp0).mpr hp1
  linarith

/-- A purely rational substitute for the usual exponential sieve bound. -/
theorem sieveWeight_mul_mass_le_one {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    sieveWeight F * (1 + reciprocalMass F) ≤ 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [sieveWeight, reciprocalMass]
  | @insert p F hp ih =>
    have hpPrime := hF p (Finset.mem_insert_self p F)
    have hFPrime : ∀ q ∈ F, q.Prime := fun q hq => hF q (Finset.mem_insert_of_mem hq)
    have hbound := ih hFPrime
    have hw := sieveWeight_nonneg hFPrime
    have hs := reciprocalMass_nonneg F
    have hx : 0 ≤ (p : ℚ)⁻¹ := by positivity
    have hstep : (1 - (p : ℚ)⁻¹) * (1 + ((p : ℚ)⁻¹ + reciprocalMass F)) ≤
        1 + reciprocalMass F := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hstep hw
    simpa [sieveWeight, reciprocalMass, Finset.prod_insert hp, Finset.sum_insert hp,
      mul_assoc, mul_left_comm, mul_comm] using le_trans hmul hbound

theorem totient_primeProduct {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    ((∏ p ∈ F, p).totient : ℚ) = (∏ p ∈ F, p : ℕ) * sieveWeight F := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [sieveWeight]
  | @insert p F hp ih =>
    have hpPrime := hF p (Finset.mem_insert_self p F)
    have hFPrime : ∀ q ∈ F, q.Prime := fun q hq => hF q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ F, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hpPrime (hFPrime q hq)).mpr (by
        intro hpq
        exact hp (hpq ▸ hq))
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    have hpred : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      exact_mod_cast Nat.cast_sub hpPrime.one_lt.le
    rw [Finset.prod_insert hp, Nat.totient_mul hcop, Nat.totient_prime hpPrime,
      Nat.cast_mul, hpred, ih hFPrime]
    simp only [sieveWeight, Finset.prod_insert hp, Nat.cast_mul]
    field_simp

/-- A fixed integer error is eventually smaller than any positive rational
multiple of the counting parameter. This avoids analytic imports. -/
theorem eventually_const_le_mul (c : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (c : ℚ) ≤ δ * X := by
  have hden : (δ.den : ℚ) ≠ 0 := by exact_mod_cast δ.den_pos.ne'
  have hnum : (1 : ℚ) ≤ δ.num := by
    exact_mod_cast (show (1 : ℤ) ≤ δ.num by have := Rat.num_pos.mpr hδ; omega)
  have heq : δ * δ.den = δ.num :=
    (eq_div_iff hden).mp (Rat.num_div_den δ).symm
  refine ⟨c * δ.den, fun X hX => ?_⟩
  have hX' : ((c * δ.den : ℕ) : ℚ) ≤ X := by exact_mod_cast hX
  have hc : (0 : ℚ) ≤ c := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnum hc
  have hlarge := mul_le_mul_of_nonneg_left hX' hδ.le
  push_cast at hlarge
  nlinarith

def avoids (P : Set ℕ) : Set ℕ := {n | ∀ p ∈ P, ¬p ∣ n}

theorem count_avoids_le {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime)
    {F : Finset ℕ} (hF : ∀ p ∈ F, p ∈ P) (X : ℕ) :
    (count (avoids P) X : ℚ) ≤ sieveWeight F * X + (∏ p ∈ F, p : ℕ) := by
  classical
  let M : ℕ := ∏ p ∈ F, p
  have hprimes : ∀ p ∈ F, p.Prime := fun p hp => hP p (hF p hp)
  have hM : 0 < M := Finset.prod_pos fun p hp => (hprimes p hp).pos
  have hsub : avoids P ⊆ {n | M.Coprime n} := by
    intro n hn
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (hprimes p hp).coprime_iff_not_dvd.mpr (hn p (hF p hp))
  have hinterval : Finset.Icc 1 X = Finset.Ico 1 (1 + X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hc : count {n | M.Coprime n} X ≤ M.totient * (X / M + 1) := by
    simpa only [count, Set.mem_ofPred_eq, hinterval] using
      Nat.Ico_filter_coprime_le 1 X hM.ne'
  have hc' : (count (avoids P) X : ℚ) ≤ (M.totient : ℚ) * ((X / M : ℕ) + 1) := by
    exact_mod_cast (count_mono hsub X).trans hc
  have hdiv : ((X / M : ℕ) : ℚ) * M ≤ X := by
    exact_mod_cast Nat.div_mul_le_self X M
  have hw := sieveWeight_nonneg hprimes
  have htot : (M.totient : ℚ) = M * sieveWeight F := totient_primeProduct hprimes
  have htotle : (M.totient : ℚ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hdivw := mul_le_mul_of_nonneg_left hdiv hw
  nlinarith [hc']

/-- The elementary divergent-prime sieve. Every ingredient, including the
finite residue-class count, is proved from the imported mathlib theorems. -/
theorem densityZero_avoids {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ReciprocalDiverges P) : DensityZero (avoids P) := by
  intro ε hε
  obtain ⟨F, hF, hmass⟩ := hdiv (2 / ε)
  have hprimes : ∀ p ∈ F, p.Prime := fun p hp => hP p (hF p hp)
  have hw := sieveWeight_nonneg hprimes
  have hprod := sieveWeight_mul_mass_le_one hprimes
  have hεmass : 2 < ε * reciprocalMass F := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hmass
  have hwε : sieveWeight F ≤ ε / 2 := by nlinarith
  obtain ⟨N, hN⟩ := eventually_const_le_mul (∏ p ∈ F, p) (show 0 < ε / 2 by positivity)
  refine ⟨N, fun X hX => ?_⟩
  have hcount := count_avoids_le hP hF X
  have hconst := hN X hX
  have hwX := mul_le_mul_of_nonneg_right hwε (show (0 : ℚ) ≤ X by positivity)
  linarith

theorem ReciprocalDiverges.diff_finset {P : Set ℕ} (hdiv : ReciprocalDiverges P)
    (F : Finset ℕ) : ReciprocalDiverges (P \ (F : Set ℕ)) := by
  classical
  intro C
  obtain ⟨G, hG, hmass⟩ := hdiv (C + reciprocalMass F)
  refine ⟨G \ F, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpG, hpF⟩ := Finset.mem_sdiff.mp hp
    exact ⟨hG p hpG, hpF⟩
  · have hinter : reciprocalMass (G ∩ F) ≤ reciprocalMass F := by
      unfold reciprocalMass
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intros
      positivity
    have hsplit : reciprocalMass (G ∩ F) + reciprocalMass (G \ F) =
        reciprocalMass G := Finset.sum_inter_add_sum_sdiff G F _
    linarith

def atMostOne (P : Set ℕ) : Set ℕ :=
  {n | ∀ p ∈ P, ∀ q ∈ P, p ∣ n → q ∣ n → p = q}

/-- Integers divisible by at most one distinct member of a divergent prime set
also have density zero. Arbitrary powers of the permitted prime are allowed. -/
theorem densityZero_atMostOne {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ReciprocalDiverges P) : DensityZero (atMostOne P) := by
  classical
  intro ε hε
  obtain ⟨F, hF, hmass⟩ := hdiv (3 / ε)
  have hprimes : ∀ p ∈ F, p.Prime := fun p hp => hP p (hF p hp)
  have hdiff : DensityZero (avoids (P \ (F : Set ℕ))) :=
    densityZero_avoids (fun p hp => hP p hp.1) (hdiv.diff_finset F)
  have hsub : atMostOne P ⊆ avoids (F : Set ℕ) ∪ avoids (P \ (F : Set ℕ)) := by
    intro n hn
    by_cases h : ∀ p ∈ F, ¬p ∣ n
    · exact Or.inl h
    · push Not at h
      obtain ⟨p, hpF, hpd⟩ := h
      right
      intro q hq hqd
      have hpq := hn p (hF p hpF) q hq.1 hpd hqd
      exact hq.2 (hpq ▸ hpF)
  have hw := sieveWeight_nonneg hprimes
  have hprod := sieveWeight_mul_mass_le_one hprimes
  have hεmass : 3 < ε * reciprocalMass F := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hmass
  have hwε : sieveWeight F ≤ ε / 3 := by nlinarith
  obtain ⟨N₁, hN₁⟩ := eventually_const_le_mul (∏ p ∈ F, p)
    (show 0 < ε / 3 by positivity)
  obtain ⟨N₂, hN₂⟩ := hdiff (ε / 3) (by positivity)
  refine ⟨max N₁ N₂, fun X hX => ?_⟩
  have hcount := count_avoids_le (P := (F : Set ℕ)) hprimes (F := F) (fun _ hp => hp) X
  have hconst := hN₁ X ((le_max_left _ _).trans hX)
  have hdiffX := hN₂ X ((le_max_right _ _).trans hX)
  have hwX := mul_le_mul_of_nonneg_right hwε (show (0 : ℚ) ≤ X by positivity)
  have hunion : (count (atMostOne P) X : ℚ) ≤
      count (avoids (F : Set ℕ)) X + count (avoids (P \ (F : Set ℕ))) X := by
    exact_mod_cast (count_mono hsub X).trans (count_union_le _ _ X)
  linarith

end NSDensity
