import NSDensity.Tails

/-!
Elementary reciprocal tails for the equally-spaced family: products of two
summable families and the grid (i+2)^(j+2). All estimates are finite rational
inequalities, without external analytic assumptions.
-/

namespace NSDensity

theorem ReciprocalTails.bounded {ι : Type*} {a : ι → ℕ} (htail : ReciprocalTails a) :
    ∃ M : ℚ, 0 < M ∧ ∀ F : Finset ι, ∑ i ∈ F, (a i : ℚ)⁻¹ ≤ M := by
  classical
  obtain ⟨J, hJ⟩ := htail 1 (by norm_num)
  refine ⟨(∑ i ∈ J, (a i : ℚ)⁻¹) + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ ∑ i ∈ J, (a i : ℚ)⁻¹ := by positivity
    linarith
  · intro F
    have htailF := hJ (F \ J) Finset.sdiff_disjoint
    have hhead : ∑ i ∈ F ∩ J, (a i : ℚ)⁻¹ ≤ ∑ i ∈ J, (a i : ℚ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => by positivity)
    have hsplit := Finset.sum_inter_add_sum_sdiff F J (fun i => (a i : ℚ)⁻¹)
    linarith

private theorem sum_product_le_rectangle {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset (ι × κ))
    (f : ι → ℚ) (g : κ → ℚ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) :
    ∑ p ∈ F, f p.1 * g p.2 ≤
      (∑ i ∈ F.image Prod.fst, f i) * ∑ j ∈ F.image Prod.snd, g j := by
  classical
  have hsub : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ι × κ => f p.1 * g p.2) (fun p _ _ => mul_nonneg (hf p.1) (hg p.2))
  calc
    _ ≤ ∑ p ∈ (F.image Prod.fst) ×ˢ (F.image Prod.snd), f p.1 * g p.2 := hsum
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- The product of two families with reciprocal tails has reciprocal tails.
The finite rectangular head and both tails are controlled explicitly. -/
theorem ReciprocalTails.mul {ι κ : Type*} {a : ι → ℕ} {b : κ → ℕ}
    (ha : ReciprocalTails a) (hb : ReciprocalTails b) :
    ReciprocalTails (fun p : ι × κ => a p.1 * b p.2) := by
  classical
  obtain ⟨M, hM, hMa⟩ := ha.bounded
  obtain ⟨N, hN, hNb⟩ := hb.bounded
  intro ε hε
  obtain ⟨I, hI⟩ := ha (ε / (2 * N)) (by positivity)
  obtain ⟨J, hJ⟩ := hb (ε / (2 * M)) (by positivity)
  refine ⟨I ×ˢ J, fun F hF => ?_⟩
  let F₁ := F.filter (fun p => p.1 ∉ I)
  let F₂ := F.filter (fun p => p.2 ∉ J)
  have hcover : F ⊆ F₁ ∪ F₂ := by
    intro p hp
    have hpout : ¬(p.1 ∈ I ∧ p.2 ∈ J) := by
      intro hpIJ
      exact Finset.disjoint_left.mp hF hp (Finset.mem_product.mpr hpIJ)
    simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter]
    by_cases hpI : p.1 ∈ I
    · exact Or.inr ⟨hp, fun hpJ => hpout ⟨hpI, hpJ⟩⟩
    · exact Or.inl ⟨hp, hpI⟩
  let f := fun p : ι × κ => (a p.1 : ℚ)⁻¹ * (b p.2 : ℚ)⁻¹
  have hnonneg : ∀ p, 0 ≤ f p := fun p => by dsimp [f]; positivity
  have hfinite : ∑ p ∈ F, f p ≤ (∑ p ∈ F₁, f p) + ∑ p ∈ F₂, f p := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (f := f) (fun p _ _ => hnonneg p)
    have hunion := Finset.sum_union_inter (s₁ := F₁) (s₂ := F₂) (f := f)
    have hinter : 0 ≤ ∑ p ∈ F₁ ∩ F₂, f p := Finset.sum_nonneg (fun p _ => hnonneg p)
    linarith
  have hleft : Disjoint (F₁.image Prod.fst) I := by
    apply Finset.disjoint_left.mpr
    intro i hi hiI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hp).2 hiI
  have hright : Disjoint (F₂.image Prod.snd) J := by
    apply Finset.disjoint_left.mpr
    intro j hj hjJ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hp).2 hjJ
  have hrect₁ := sum_product_le_rectangle F₁ (fun i => (a i : ℚ)⁻¹)
    (fun j => (b j : ℚ)⁻¹) (fun _ => by positivity) (fun _ => by positivity)
  have hrect₂ := sum_product_le_rectangle F₂ (fun i => (a i : ℚ)⁻¹)
    (fun j => (b j : ℚ)⁻¹) (fun _ => by positivity) (fun _ => by positivity)
  have hsum₁ := hI _ hleft
  have hsum₂ := hJ _ hright
  have htotal₁ := hNb (F₁.image Prod.snd)
  have htotal₂ := hMa (F₂.image Prod.fst)
  have hnonneg₁ : 0 ≤ ∑ i ∈ F₁.image Prod.fst, (a i : ℚ)⁻¹ := by positivity
  have hnonneg₂ : 0 ≤ ∑ j ∈ F₂.image Prod.snd, (b j : ℚ)⁻¹ := by positivity
  have hmul₁ := mul_le_mul_of_nonneg_left htotal₁ hnonneg₁
  have hmul₂ := mul_le_mul_of_nonneg_right htotal₂ hnonneg₂
  have hsmall₁ : (ε / (2 * N)) * N = ε / 2 := by field_simp
  have hsmall₂ : M * (ε / (2 * M)) = ε / 2 := by field_simp
  have hmass₁ := mul_le_mul_of_nonneg_right hsum₁ hN.le
  have hmass₂ := mul_le_mul_of_nonneg_left hsum₂ hM.le
  have hsum : ∑ p ∈ F, f p ≤ ε := by
    dsimp [f] at hfinite ⊢
    nlinarith
  simpa only [f, Nat.cast_mul, mul_inv_rev, mul_comm] using hsum

private theorem successive_inv (n : ℕ) :
    (((n + 1) * (n + 2) : ℕ) : ℚ)⁻¹ = (n + 1 : ℚ)⁻¹ - (n + 2 : ℚ)⁻¹ := by
  have h₁ : (n + 1 : ℚ) ≠ 0 := by positivity
  have h₂ : (n + 2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

private theorem successive_sum_range (J k : ℕ) :
    ∑ n ∈ Finset.range k, (((n + J + 1) * (n + J + 2) : ℕ) : ℚ)⁻¹ =
      (J + 1 : ℚ)⁻¹ - (k + J + 1 : ℚ)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, successive_inv]
    push_cast
    have heq : ((k : ℚ) + 1 + J + 1) = (k + J + 2 : ℚ) := by ring
    rw [heq]
    ring

theorem successive_tail_le (F : Finset ℕ) (J : ℕ) (hF : ∀ n ∈ F, J ≤ n) :
    ∑ n ∈ F, (((n + 1) * (n + 2) : ℕ) : ℚ)⁻¹ ≤ (J + 1 : ℚ)⁻¹ := by
  classical
  have hinj : ∀ n ∈ F, ∀ m ∈ F, n - J = m - J → n = m := by
    intro n hn m hm hnm
    have hnJ := hF n hn
    have hmJ := hF m hm
    omega
  let G := F.image (fun n => n - J)
  have hrepr : ∑ n ∈ F, (((n + 1) * (n + 2) : ℕ) : ℚ)⁻¹ =
      ∑ k ∈ G, (((k + J + 1) * (k + J + 2) : ℕ) : ℚ)⁻¹ := by
    rw [show G = F.image (fun n => n - J) from rfl, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.sub_add_cancel (hF n hn)]
  have hsub : G ⊆ Finset.range (G.sup id + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun n => (((n + J + 1) * (n + J + 2) : ℕ) : ℚ)⁻¹)
    (fun _ _ _ => by positivity)
  rw [successive_sum_range] at hsum
  push_cast at hsum
  rw [hrepr]
  push_cast
  have hpos : 0 ≤ (G.sup id + 1 + J + 1 : ℚ)⁻¹ := by positivity
  linarith

theorem reciprocalTails_successive_mul :
    ReciprocalTails (fun i : ℕ => (i + 1) * (i + 2)) := by
  classical
  intro ε hε
  refine ⟨Finset.range ε.den, fun F hF => ?_⟩
  have hFJ : ∀ n ∈ F, ε.den ≤ n := by
    intro n hn
    by_contra h
    exact Finset.disjoint_left.mp hF hn (Finset.mem_range.mpr (by omega))
  have htail := successive_tail_le F ε.den hFJ
  have hden : (ε.den : ℚ) ≠ 0 := by exact_mod_cast ε.den_pos.ne'
  have hnum : (1 : ℚ) ≤ ε.num := by
    exact_mod_cast (show (1 : ℤ) ≤ ε.num by have := Rat.num_pos.mpr hε; omega)
  have heq : ε * ε.den = ε.num := (eq_div_iff hden).mp (Rat.num_div_den ε).symm
  have hsmall : (ε.den + 1 : ℚ)⁻¹ ≤ ε := by
    have hsmalldiv : 1 / (ε.den + 1 : ℚ) ≤ ε := by
      apply (div_le_iff₀ (show (0 : ℚ) < ε.den + 1 by positivity)).mpr
      nlinarith
    simpa only [one_div] using hsmalldiv
  exact htail.trans hsmall

theorem reciprocalTails_powerGrid :
    ReciprocalTails (fun p : ℕ × ℕ => (p.1 + 2) ^ (p.2 + 2)) := by
  apply (reciprocalTails_successive_mul.mul reciprocalTails_two_pow).mono
    (fun p => by positivity)
  intro p
  have hbase : 2 ≤ p.1 + 2 := by omega
  have hpow : 2 ^ p.2 ≤ (p.1 + 2) ^ p.2 := Nat.pow_le_pow_left hbase _
  have hquad : (p.1 + 1) * (p.1 + 2) ≤ (p.1 + 2) ^ 2 := by nlinarith
  calc
    (p.1 + 1) * (p.1 + 2) * 2 ^ p.2 ≤ (p.1 + 2) ^ 2 * (p.1 + 2) ^ p.2 :=
      Nat.mul_le_mul hquad hpow
    _ = (p.1 + 2) ^ (p.2 + 2) := by
      rw [← pow_add]
      congr 1
      omega

end NSDensity
