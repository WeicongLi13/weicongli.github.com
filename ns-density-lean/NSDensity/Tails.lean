import NSDensity.Basic
import NSDensity.Sieve
import Mathlib.Data.Set.Finite.Lattice

/-!
Counting closure principles for zero natural density. Infinite unions are
controlled by actual finite reciprocal tails; no countable-union principle
for arbitrary zero-density sets is assumed.
-/

namespace NSDensity

def scaled (a : ℕ) (A : Set ℕ) : Set ℕ := {n | ∃ u ∈ A, n = a * u}

theorem count_scaled_le (a : ℕ) (ha : 0 < a) (A : Set ℕ) (X : ℕ) :
    count (scaled a A) X ≤ count A X := by
  classical
  unfold count
  apply le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun u => a * u))
  intro n hn
  obtain ⟨hnI, u, huA, hnu⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnpos, hnX⟩ := Finset.mem_Icc.mp hnI
  have hu0 : 1 ≤ u := by
    by_contra h
    have hu : u = 0 := by omega
    simp [hnu, hu] at hnpos
  have hun : u ≤ n := by
    rw [hnu]
    exact Nat.le_mul_of_pos_left u ha
  apply Finset.mem_image.mpr
  exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hu0, hun.trans hnX⟩, huA⟩,
    hnu.symm⟩

theorem DensityZero.scaled {A : Set ℕ} (hA : DensityZero A) (a : ℕ) (ha : 0 < a) :
    DensityZero (scaled a A) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun X hX => le_trans ?_ (hN X hX)⟩
  exact_mod_cast count_scaled_le a ha A X

/-- Only finitely many members of any indexed family are needed to cover the
union inside a fixed finite counting interval. -/
theorem finite_count_cover {ι : Type*} (A : ι → Set ℕ) (X : ℕ) :
    ∃ F : Finset ι, count (⋃ i, A i) X = count (⋃ i ∈ F, A i) X := by
  classical
  let S : Set ℕ := (↑(Finset.Icc 1 X) : Set ℕ) ∩ ⋃ i, A i
  have hS : S.Finite := (Finset.Icc 1 X).finite_toSet.subset Set.inter_subset_left
  obtain ⟨J, hJfin, hJ⟩ := Set.finite_subset_iUnion hS Set.inter_subset_right
  refine ⟨hJfin.toFinset, ?_⟩
  unfold count
  congr 1
  ext n
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hnI, hnA⟩
    have hnJ := hJ (show n ∈ S from ⟨hnI, hnA⟩)
    obtain ⟨i, hi, hni⟩ := Set.mem_iUnion₂.mp hnJ
    exact ⟨hnI, Set.mem_iUnion₂.mpr ⟨i, hJfin.mem_toFinset.mpr hi, hni⟩⟩
  · intro ⟨hnI, hnA⟩
    obtain ⟨i, _, hni⟩ := Set.mem_iUnion₂.mp hnA
    exact ⟨hnI, Set.mem_iUnion.mpr ⟨i, hni⟩⟩

/-- Rational form of the finite reciprocal-tail condition, usable for any
index type, including pairs of natural numbers and prime/exponent pairs. -/
def ReciprocalTails {ι : Type*} (a : ι → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ J : Finset ι, ∀ F : Finset ι, Disjoint F J →
    ∑ i ∈ F, (a i : ℚ)⁻¹ ≤ ε

theorem count_le_reciprocal_mul {A : Set ℕ} {a : ℕ} (ha : 0 < a)
    (hA : A ⊆ {n | a ∣ n}) (X : ℕ) :
    (count A X : ℚ) ≤ (X : ℚ) * (a : ℚ)⁻¹ := by
  have hcount : (count A X : ℚ) ≤ (X / a : ℕ) := by
    exact_mod_cast count_le_div_of_subset_multiples hA X
  have hdiv : ((X / a : ℕ) : ℚ) * a ≤ X := by
    exact_mod_cast Nat.div_mul_le_self X a
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hdiv' : ((X / a : ℕ) : ℚ) ≤ (X : ℚ) / a := (le_div_iff₀ haQ).mpr hdiv
  simpa only [div_eq_mul_inv] using hcount.trans hdiv'

/-- The summable-multiples tail lemma. Both the finite-head approximation and
the counting bound on the entire infinite tail are proved here. -/
theorem densityZero_iUnion_of_reciprocalTails {ι : Type*} (A : ι → Set ℕ)
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (hA : ∀ i, A i ⊆ {n | a i ∣ n})
    (hzero : ∀ i, DensityZero (A i)) (htail : ReciprocalTails a) :
    DensityZero (⋃ i, A i) := by
  classical
  apply densityZero_of_approximation
  intro ε hε
  obtain ⟨J, hJ⟩ := htail ε hε
  refine ⟨⋃ i ∈ J, A i, DensityZero.biUnion_finset J A (fun i _ => hzero i), ?_⟩
  intro X
  obtain ⟨F, hcover⟩ := finite_count_cover A X
  have hsub : (⋃ i ∈ F, A i) ⊆ (⋃ i ∈ J, A i) ∪ (⋃ i ∈ F \ J, A i) := by
    intro n hn
    obtain ⟨i, hiF, hni⟩ := Set.mem_iUnion₂.mp hn
    by_cases hiJ : i ∈ J
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hiJ, hni⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hiF, hiJ⟩, hni⟩)
  have hcount : count (⋃ i, A i) X ≤ count (⋃ i ∈ J, A i) X +
      ∑ i ∈ F \ J, count (A i) X := by
    rw [hcover]
    exact (count_mono hsub X).trans ((count_union_le _ _ X).trans
      (Nat.add_le_add_left (count_biUnion_finset_le (F \ J) A X) _))
  have hcountQ : (count (⋃ i, A i) X : ℚ) ≤ count (⋃ i ∈ J, A i) X +
      ∑ i ∈ F \ J, (count (A i) X : ℚ) := by exact_mod_cast hcount
  have hterms : ∑ i ∈ F \ J, (count (A i) X : ℚ) ≤
      (X : ℚ) * ∑ i ∈ F \ J, (a i : ℚ)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => count_le_reciprocal_mul (ha i) (hA i) X
  have htailbound := hJ (F \ J) Finset.sdiff_disjoint
  have hsmall := mul_le_mul_of_nonneg_left htailbound (show (0 : ℚ) ≤ X by positivity)
  nlinarith

private theorem dyadic_sum_range (k : ℕ) :
    ∑ n ∈ Finset.range k, (1 / 2 : ℚ) ^ n = 2 * (1 - (1 / 2 : ℚ) ^ k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem dyadic_sum_le_two (F : Finset ℕ) :
    ∑ n ∈ F, (1 / 2 : ℚ) ^ n ≤ 2 := by
  have hsub : F ⊆ Finset.range (F.sup id + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  have hsum : ∑ n ∈ F, (1 / 2 : ℚ) ^ n ≤
      ∑ n ∈ Finset.range (F.sup id + 1), (1 / 2 : ℚ) ^ n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [dyadic_sum_range] at hsum
  have hp : 0 ≤ (1 / 2 : ℚ) ^ (F.sup id + 1) := by positivity
  linarith

theorem dyadic_tail_le (F : Finset ℕ) (J : ℕ) (hF : ∀ n ∈ F, J ≤ n) :
    ∑ n ∈ F, (1 / 2 : ℚ) ^ n ≤ 2 * (1 / 2 : ℚ) ^ J := by
  classical
  have hinj : ∀ n ∈ F, ∀ m ∈ F, n - J = m - J → n = m := by
    intro n hn m hm hnm
    have hnJ := hF n hn
    have hmJ := hF m hm
    omega
  have hrepr : ∑ n ∈ F, (1 / 2 : ℚ) ^ n =
      (1 / 2 : ℚ) ^ J * ∑ k ∈ F.image (fun n => n - J), (1 / 2 : ℚ) ^ k := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← pow_add, Nat.add_sub_of_le (hF n hn)]
  rw [hrepr]
  have hsum := mul_le_mul_of_nonneg_left (dyadic_sum_le_two (F.image (fun n => n - J)))
    (show (0 : ℚ) ≤ (1 / 2 : ℚ) ^ J by positivity)
  simpa [mul_comm] using hsum

/-- Explicit geometric tails, proved by finite sums over the rationals. -/
theorem reciprocalTails_two_pow : ReciprocalTails (fun n : ℕ => 2 ^ n) := by
  classical
  intro ε hε
  let J := 2 * ε.den + 1
  refine ⟨Finset.range J, fun F hF => ?_⟩
  have hFJ : ∀ n ∈ F, J ≤ n := by
    intro n hn
    by_contra h
    have hnJ : n ∈ Finset.range J := Finset.mem_range.mpr (by omega)
    exact Finset.disjoint_left.mp hF hn hnJ
  have htail := dyadic_tail_le F J hFJ
  have hden : (ε.den : ℚ) ≠ 0 := by exact_mod_cast ε.den_pos.ne'
  have hnum : (1 : ℚ) ≤ ε.num := by
    exact_mod_cast (show (1 : ℤ) ≤ ε.num by have := Rat.num_pos.mpr hε; omega)
  have heq : ε * ε.den = ε.num := (eq_div_iff hden).mp (Rat.num_div_den ε).symm
  have hpow : 2 * ε.den ≤ 2 ^ J := by
    have hJ := J.lt_two_pow_self
    dsimp [J] at hJ ⊢
    omega
  have hpowQ : (2 : ℚ) * ε.den ≤ (2 : ℚ) ^ J := by exact_mod_cast hpow
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ J := by positivity
  have hsmall : 2 / (2 : ℚ) ^ J ≤ ε := by
    apply (div_le_iff₀ hpowpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpowQ hε.le]
  have hnorm : (∑ n ∈ F, ((2 ^ n : ℕ) : ℚ)⁻¹) =
      ∑ n ∈ F, (1 / 2 : ℚ) ^ n := by simp [inv_pow]
  rw [hnorm]
  have hnormJ : 2 * (1 / 2 : ℚ) ^ J = 2 / (2 : ℚ) ^ J := by
    simp [div_eq_mul_inv, inv_pow]
  exact htail.trans (hnormJ ▸ hsmall)

theorem ReciprocalTails.mono {ι : Type*} {a b : ι → ℕ} (htail : ReciprocalTails a)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) : ReciprocalTails b := by
  intro ε hε
  obtain ⟨J, hJ⟩ := htail ε hε
  refine ⟨J, fun F hF => le_trans ?_ (hJ F hF)⟩
  apply Finset.sum_le_sum
  intro i _
  have hai : (0 : ℚ) < a i := by exact_mod_cast ha i
  have habi : (a i : ℚ) ≤ b i := by exact_mod_cast hab i
  exact inv_anti₀ hai habi

theorem reciprocalTails_of_inv_le_dyadic (a : ℕ → ℕ)
    (hbound : ∀ n, (a n : ℚ)⁻¹ ≤ (1 / 2 : ℚ) ^ n) : ReciprocalTails a := by
  intro ε hε
  obtain ⟨J, hJ⟩ := reciprocalTails_two_pow ε hε
  refine ⟨J, fun F hF => le_trans ?_ (hJ F hF)⟩
  apply Finset.sum_le_sum
  intro n _
  simpa [inv_pow] using hbound n

private theorem exists_dyadic_small (c : ℕ) {ε : ℚ} (hε : 0 < ε) :
    ∃ K : ℕ, (c : ℚ) * (1 / 2 : ℚ) ^ K ≤ ε := by
  let K := c * ε.den + 1
  refine ⟨K, ?_⟩
  have hden : (ε.den : ℚ) ≠ 0 := by exact_mod_cast ε.den_pos.ne'
  have hnum : (1 : ℚ) ≤ ε.num := by
    exact_mod_cast (show (1 : ℤ) ≤ ε.num by have := Rat.num_pos.mpr hε; omega)
  have heq : ε * ε.den = ε.num := (eq_div_iff hden).mp (Rat.num_div_den ε).symm
  have hpow : c * ε.den ≤ 2 ^ K := by
    have hK := K.lt_two_pow_self
    dsimp [K] at hK ⊢
    omega
  have hpowQ : (c : ℚ) * ε.den ≤ (2 : ℚ) ^ K := by exact_mod_cast hpow
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ K := by positivity
  have hsmall : (c : ℚ) / (2 : ℚ) ^ K ≤ ε := by
    apply (div_le_iff₀ hpowpos).mpr
    have hc : (0 : ℚ) ≤ c := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpowQ hε.le]
  simpa [div_eq_mul_inv, inv_pow] using hsmall

private theorem dyadic_sum_le_rectangle (F : Finset (ℕ × ℕ)) :
    ∑ p ∈ F, (1 / 2 : ℚ) ^ (p.1 + p.2) ≤
      (∑ i ∈ F.image Prod.fst, (1 / 2 : ℚ) ^ i) *
        ∑ j ∈ F.image Prod.snd, (1 / 2 : ℚ) ^ j := by
  classical
  have hsub : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ℕ × ℕ => (1 / 2 : ℚ) ^ (p.1 + p.2)) (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ p ∈ (F.image Prod.fst) ×ˢ (F.image Prod.snd),
        (1 / 2 : ℚ) ^ (p.1 + p.2) := hsum
    _ = _ := by
      rw [Finset.sum_product]
      simp only [pow_add]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

theorem reciprocalTails_of_inv_le_dyadic₂ (a : (ℕ × ℕ) → ℕ)
    (hbound : ∀ p, (a p : ℚ)⁻¹ ≤ (1 / 2 : ℚ) ^ (p.1 + p.2)) :
    ReciprocalTails a := by
  classical
  intro ε hε
  obtain ⟨K, hK⟩ := exists_dyadic_small 8 hε
  refine ⟨(Finset.range K) ×ˢ (Finset.range K), fun F hF => ?_⟩
  let F₁ := F.filter (fun p => K ≤ p.1)
  let F₂ := F.filter (fun p => K ≤ p.2)
  have hcover : F ⊆ F₁ ∪ F₂ := by
    intro p hp
    have hpout : ¬(p.1 < K ∧ p.2 < K) := by
      intro hpK
      exact Finset.disjoint_left.mp hF hp (by simpa using hpK)
    simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter]
    by_cases hp₁ : K ≤ p.1
    · exact Or.inl ⟨hp, hp₁⟩
    · exact Or.inr ⟨hp, by omega⟩
  have hfinite : ∑ p ∈ F, (1 / 2 : ℚ) ^ (p.1 + p.2) ≤
      (∑ p ∈ F₁, (1 / 2 : ℚ) ^ (p.1 + p.2)) +
        ∑ p ∈ F₂, (1 / 2 : ℚ) ^ (p.1 + p.2) := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (f := fun p : ℕ × ℕ => (1 / 2 : ℚ) ^ (p.1 + p.2)) (fun _ _ _ => by positivity)
    have hunion := Finset.sum_union_inter (s₁ := F₁) (s₂ := F₂)
      (f := fun p : ℕ × ℕ => (1 / 2 : ℚ) ^ (p.1 + p.2))
    have hinter : 0 ≤ ∑ p ∈ F₁ ∩ F₂, (1 / 2 : ℚ) ^ (p.1 + p.2) := by positivity
    linarith
  have hfst : ∑ i ∈ F₁.image Prod.fst, (1 / 2 : ℚ) ^ i ≤
      2 * (1 / 2 : ℚ) ^ K := by
    apply dyadic_tail_le
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hp).2
  have hsnd : ∑ j ∈ F₂.image Prod.snd, (1 / 2 : ℚ) ^ j ≤
      2 * (1 / 2 : ℚ) ^ K := by
    apply dyadic_tail_le
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hp).2
  have hrect₁ := dyadic_sum_le_rectangle F₁
  have hrect₂ := dyadic_sum_le_rectangle F₂
  have hsum₁ := dyadic_sum_le_two (F₁.image Prod.snd)
  have hsum₂ := dyadic_sum_le_two (F₂.image Prod.fst)
  have hnonneg₁ : 0 ≤ ∑ i ∈ F₁.image Prod.fst, (1 / 2 : ℚ) ^ i := by positivity
  have hnonneg₂ : 0 ≤ ∑ j ∈ F₂.image Prod.snd, (1 / 2 : ℚ) ^ j := by positivity
  have hmul₁ := mul_le_mul_of_nonneg_left hsum₁ hnonneg₁
  have hmul₂ := mul_le_mul_of_nonneg_right hsum₂ hnonneg₂
  have hsum : ∑ p ∈ F, (1 / 2 : ℚ) ^ (p.1 + p.2) ≤
      8 * (1 / 2 : ℚ) ^ K := by nlinarith
  exact (Finset.sum_le_sum (fun p _ => hbound p)).trans (hsum.trans hK)

theorem reciprocalTails_of_two_pow_le (a : ℕ → ℕ)
    (hbound : ∀ n, 2 ^ n ≤ a n) : ReciprocalTails a :=
  reciprocalTails_two_pow.mono (fun n => by positivity) hbound

theorem reciprocalTails_of_two_pow_add_le (a : (ℕ × ℕ) → ℕ)
    (hbound : ∀ p, 2 ^ (p.1 + p.2) ≤ a p) : ReciprocalTails a := by
  apply reciprocalTails_of_inv_le_dyadic₂
  intro p
  have hp : (0 : ℚ) < (2 : ℚ) ^ (p.1 + p.2) := by positivity
  have hle : (2 : ℚ) ^ (p.1 + p.2) ≤ a p := by exact_mod_cast hbound p
  simpa [inv_pow] using inv_anti₀ hp hle

end NSDensity
