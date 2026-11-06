import NSDensity.CodeModelGenerated

namespace NSDensity.Concrete

variable {n : ℕ} [NeZero n]

/-- Affine permutations of the cyclic coordinate labels. -/
def affinePerm (u : (ZMod n)ˣ) (b : ZMod n) : Equiv.Perm (Fin n) where
  toFun i := ⟨((u : ZMod n) * (i.val : ZMod n) + b).val, ZMod.val_lt _⟩
  invFun i := ⟨((↑u⁻¹ : ZMod n) * ((i.val : ZMod n) - b)).val, ZMod.val_lt _⟩
  left_inv i := by
    apply Fin.ext
    simp [← mul_assoc, Nat.mod_eq_of_lt i.isLt]
  right_inv i := by
    apply Fin.ext
    simp [mul_sub, ← mul_assoc, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem affinePerm_apply (u : (ZMod n)ˣ) (b : ZMod n) (i : Fin n) :
    ((affinePerm u b i).val : ZMod n) = u * (i.val : ZMod n) + b := by
  exact ZMod.natCast_zmod_val _

omit [NeZero n] in
theorem fin_eq_of_zmod_eq {i j : Fin n}
    (h : (i.val : ZMod n) = (j.val : ZMod n)) : i = j := by
  apply Fin.ext
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
    using congrArg ZMod.val h

theorem affinePerm_mul (u v : (ZMod n)ˣ) (b c : ZMod n) :
    affinePerm u b * affinePerm v c = affinePerm (u*v) ((u : ZMod n)*c+b) := by
  apply Equiv.ext
  intro i
  apply fin_eq_of_zmod_eq
  change ((affinePerm u b (affinePerm v c i)).val : ZMod n) = _
  simp only [affinePerm_apply, Units.val_mul]
  ring

@[simp] theorem affinePerm_one : affinePerm (1 : (ZMod n)ˣ) 0 = 1 := by
  apply Equiv.ext
  intro i
  apply fin_eq_of_zmod_eq
  simp

theorem affinePerm_injective :
    Function.Injective (fun z : (ZMod n)ˣ × ZMod n => affinePerm z.1 z.2) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ h
  have hb : b = c := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ ⟨0, NeZero.pos n⟩).val : ZMod n)) h
    simpa using this
  have hu : (u : ZMod n) = v := by
    let i : Fin n := ⟨(1 : ZMod n).val, ZMod.val_lt _⟩
    have := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ i).val : ZMod n)) h
    simpa [i, hb] using this
  exact Prod.ext (Units.ext hu) hb

/-- The standard permutations as a subgroup, with their literal affine action. -/
def standardGroup (q : ℕ) (hcop : Nat.Coprime q n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∃ u ∈ Subgroup.zpowers (ZMod.unitOfCoprime q hcop),
    ∃ b, σ = affinePerm u b}
  one_mem' := ⟨1, Subgroup.one_mem _, 0, affinePerm_one.symm⟩
  mul_mem' := by
    rintro σ τ ⟨u, hu, b, rfl⟩ ⟨v, hv, c, rfl⟩
    exact ⟨u*v, Subgroup.mul_mem _ hu hv, _, affinePerm_mul u v b c⟩
  inv_mem' := by
    rintro σ ⟨u, hu, b, rfl⟩
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, -(↑u⁻¹ : ZMod n)*b, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [affinePerm_mul]
    simp [← mul_assoc]

theorem mem_standardGroup_iff (q : ℕ) (hcop : Nat.Coprime q n)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ standardGroup q hcop ↔ standardPermutation q n σ := by
  constructor
  · rintro ⟨u, hu, b, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hu
    refine ⟨j, b, fun i => ?_⟩
    simp [affinePerm_apply, ZMod.coe_unitOfCoprime]
  · rintro ⟨j, b, hσ⟩
    refine ⟨ZMod.unitOfCoprime q hcop ^ j,
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j, b, ?_⟩
    apply Equiv.ext
    intro i
    apply fin_eq_of_zmod_eq
    simpa [affinePerm_apply, ZMod.coe_unitOfCoprime] using hσ i

noncomputable def standardGroupEquiv (q : ℕ) (hcop : Nat.Coprime q n) :
    (Subgroup.zpowers (ZMod.unitOfCoprime q hcop)) × ZMod n ≃ standardGroup q hcop :=
  Equiv.ofBijective (fun z => ⟨affinePerm z.1.val z.2, z.1.val, z.1.property, z.2, rfl⟩)
    ⟨by
      rintro ⟨u,b⟩ ⟨v,c⟩ h
      have hab : affinePerm (u : (ZMod n)ˣ) b = affinePerm (v : (ZMod n)ˣ) c :=
        congrArg Subtype.val h
      have huv : ((u : (ZMod n)ˣ), b) = ((v : (ZMod n)ˣ), c) :=
        affinePerm_injective hab
      exact Prod.ext (Subtype.ext (congrArg Prod.fst huv))
        (congrArg (fun z : (ZMod n)ˣ × ZMod n => z.2) huv),
    by
      rintro ⟨σ,u,hu,b,rfl⟩
      exact ⟨(⟨u,hu⟩,b), rfl⟩⟩

theorem standardGroup_card (q : ℕ) (hcop : Nat.Coprime q n) :
    Nat.card (standardGroup q hcop) = n * orderOf (q : ZMod n) := by
  classical
  rw [← Nat.card_congr (standardGroupEquiv q hcop), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Subgroup.zpowers _), Fintype.card_zpowers,
    Nat.card_zmod, ← orderOf_units, ZMod.coe_unitOfCoprime, mul_comm]

def cyclicShift : Equiv.Perm (Fin n) := affinePerm 1 1

def frobeniusPermutation (q : ℕ) (hcop : Nat.Coprime q n) : Equiv.Perm (Fin n) :=
  affinePerm (ZMod.unitOfCoprime q hcop) 0

theorem affinePerm_translation_pow (b : ZMod n) (k : ℕ) :
    affinePerm 1 b ^ k = affinePerm 1 ((k : ZMod n)*b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, affinePerm_mul]
    simp [Nat.cast_add, add_mul, add_comm]

theorem affinePerm_scaling_pow (u : (ZMod n)ˣ) (k : ℕ) :
    affinePerm u 0 ^ k = affinePerm (u^k) 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, affinePerm_mul]; simp [pow_succ]

theorem standardGroup_eq_closure (q : ℕ) (hcop : Nat.Coprime q n) :
    standardGroup q hcop =
      Subgroup.closure {cyclicShift (n := n), frobeniusPermutation q hcop} := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨j,b,hσ⟩ := (mem_standardGroup_iff q hcop σ).mp hσ
    have hform : σ = cyclicShift ^ b.val * frobeniusPermutation q hcop ^ j := by
      apply Equiv.ext
      intro i
      apply fin_eq_of_zmod_eq
      simpa [cyclicShift, frobeniusPermutation, affinePerm_translation_pow,
        affinePerm_scaling_pow, affinePerm_mul, ZMod.coe_unitOfCoprime]
        using hσ i
    rw [hform]
    apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · apply (Subgroup.closure_le _).2
    intro σ hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, 1, rfl⟩
    · exact ⟨_, Subgroup.mem_zpowers _, 0, rfl⟩

theorem cyclicShift_eq_finRotate : cyclicShift (n := n) = finRotate n := by
  apply Equiv.ext
  intro i
  apply fin_eq_of_zmod_eq
  simp [cyclicShift, finRotate_apply, Fin.val_add]

theorem affinePerm_inv (u : (ZMod n)ˣ) (b : ZMod n) :
    (affinePerm u b)⁻¹ = affinePerm u⁻¹ (-(↑u⁻¹ : ZMod n) * b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [affinePerm_mul]
  simp [← mul_assoc]

/-- Conjugating by an affine coordinate change leaves the multiplier
unchanged and changes only the translation term. -/
theorem affinePerm_conjugate (u v : (ZMod n)ˣ) (b c : ZMod n) :
    affinePerm u b * affinePerm v c * (affinePerm u b)⁻¹ =
      affinePerm v ((1 - (v : ZMod n)) * b + (u : ZMod n) * c) := by
  rw [affinePerm_inv, affinePerm_mul, affinePerm_mul]
  have huv : u * v * u⁻¹ = v := by simp
  rw [huv]
  congr 1
  simp only [Units.val_mul]
  have hu : (u : ZMod n) * (↑u⁻¹ : ZMod n) = 1 := by simp
  calc
    _ = -(↑u * ↑u⁻¹) * ↑v * b + b + ↑u * c := by ring
    _ = _ := by rw [hu]; ring

theorem affinePerm_conjugate_mem_standardGroup (q : ℕ) (hcop : Nat.Coprime q n)
    (u : (ZMod n)ˣ) (b : ZMod n) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ standardGroup q hcop) :
    affinePerm u b * σ * (affinePerm u b)⁻¹ ∈ standardGroup q hcop := by
  obtain ⟨v, hv, c, rfl⟩ := hσ
  exact ⟨v, hv, _, affinePerm_conjugate u v b c⟩

/-- In particular every invertible multiplier normalizes the standard group. -/
theorem affinePerm_conjugate_standard_iff (q : ℕ) (hcop : Nat.Coprime q n)
    (u : (ZMod n)ˣ) (b : ZMod n) (σ : Equiv.Perm (Fin n)) :
    standardPermutation q n (affinePerm u b * σ * (affinePerm u b)⁻¹) ↔
      standardPermutation q n σ := by
  simp only [← mem_standardGroup_iff q hcop]
  constructor
  · intro h
    have h' := affinePerm_conjugate_mem_standardGroup q hcop u⁻¹
      (-(↑u⁻¹ : ZMod n) * b) h
    rw [← affinePerm_inv] at h'
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using h'
  · exact affinePerm_conjugate_mem_standardGroup q hcop u b

theorem affinePermutation_iff_exists_affinePerm (σ : Equiv.Perm (Fin n)) :
    affinePermutation n σ ↔ ∃ u b, σ = affinePerm u b := by
  constructor
  · rintro ⟨u, b, h⟩
    refine ⟨u, b, ?_⟩
    apply Equiv.ext
    intro i
    apply fin_eq_of_zmod_eq
    simpa using h i
  · rintro ⟨u, b, rfl⟩
    exact ⟨u, b, affinePerm_apply u b⟩

theorem affinePerm_conjugate_affine (u : (ZMod n)ˣ) (b : ZMod n)
    {σ : Equiv.Perm (Fin n)} (hσ : affinePermutation n σ) :
    affinePermutation n (affinePerm u b * σ * (affinePerm u b)⁻¹) := by
  obtain ⟨v, c, rfl⟩ := (affinePermutation_iff_exists_affinePerm σ).1 hσ
  exact (affinePermutation_iff_exists_affinePerm _).2
    ⟨v, _, affinePerm_conjugate u v b c⟩

theorem affinePerm_conjugate_affine_iff (u : (ZMod n)ˣ) (b : ZMod n)
    (σ : Equiv.Perm (Fin n)) :
    affinePermutation n (affinePerm u b * σ * (affinePerm u b)⁻¹) ↔
      affinePermutation n σ := by
  constructor
  · intro h
    have h' := affinePerm_conjugate_affine u⁻¹ (-(↑u⁻¹ : ZMod n) * b) h
    rw [← affinePerm_inv] at h'
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using h'
  · exact affinePerm_conjugate_affine u b

theorem mem_relationCode_reindex {E I : Type*} [Field E] [Fintype I]
    (F : Subfield E) (v : I → E) (τ : Equiv.Perm I) (c : I → F) :
    c ∈ relationCode F (v ∘ τ) ↔ (c ∘ τ.symm) ∈ relationCode F v := by
  simp only [mem_relationCode, Function.comp_apply]
  rw [← Equiv.sum_comp τ.symm (fun i : I => (c i : E) * v (τ i))]
  simp only [Equiv.apply_symm_apply]

theorem preservesRelations_reindex_iff {E I : Type*} [Field E] [Fintype I]
    (F : Subfield E) (v : I → E) (τ σ : Equiv.Perm I) :
    preservesRelations F (v ∘ τ) σ ↔
      preservesRelations F v (τ * σ * τ⁻¹) := by
  constructor
  · intro h c
    have hc := h (c ∘ τ)
    simp only [mem_relationCode_reindex] at hc
    simpa [Function.comp_def, Equiv.Perm.mul_apply] using hc
  · intro h c
    simp only [mem_relationCode_reindex]
    have hc := h (c ∘ τ.symm)
    simpa [Function.comp_def, Equiv.Perm.mul_apply] using hc

/-- Changing the root to a coprime power only relabels the coordinates,
and hence does not change nonstandardness. This includes length one. -/
theorem nonstandardRootCode_pow_iff {E : Type*} [Field E] (F : Subfield E)
    {a : E} {k : ℕ} (ha : orderOf a = n) (hk : Nat.Coprime k n) :
    nonstandardRootCode F n (a ^ k) ↔ nonstandardRootCode F n a := by
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime k hk
  let τ : Equiv.Perm (Fin n) := affinePerm u 0
  have hv : (fun i : Fin n => (a ^ k) ^ i.val) =
      (fun i : Fin n => a ^ i.val) ∘ τ := by
    funext i
    rw [← pow_mul]
    apply (root_pow_eq_iff_zmod (NeZero.pos n) ha).2
    simp [τ, u, affinePerm_apply, Nat.cast_mul, ZMod.coe_unitOfCoprime]
  change (∃ σ, preservesRelations F (fun i : Fin n => (a ^ k) ^ i.val) σ ∧
    ¬affinePermutation n σ) ↔ _
  rw [hv]
  constructor
  · rintro ⟨σ, hσ, hnon⟩
    refine ⟨τ * σ * τ⁻¹,
      (preservesRelations_reindex_iff F _ τ σ).1 hσ, ?_⟩
    intro h
    exact hnon ((affinePerm_conjugate_affine_iff u 0 σ).1 h)
  · rintro ⟨σ, hσ, hnon⟩
    refine ⟨τ⁻¹ * σ * τ, ?_, ?_⟩
    · apply (preservesRelations_reindex_iff F _ τ _).2
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
        mul_one] using hσ
    · intro h
      have h' := affinePerm_conjugate_affine u 0 h
      have heq : τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ := by group
      exact hnon (heq ▸ h')

/-- In a finite field, two elements of the same positive order differ by
a coprime power. -/
theorem exists_coprime_pow_eq_of_order_eq {E : Type*} [Field E] [Finite E]
    {a b : E} (ha : orderOf a = n) (hb : orderOf b = n) :
    ∃ k : ℕ, Nat.Coprime k n ∧ a ^ k = b := by
  classical
  have ha0 : a ≠ 0 :=
    (orderOf_pos_iff.mp (ha.symm ▸ NeZero.pos n)).isUnit.ne_zero
  have hb0 : b ≠ 0 :=
    (orderOf_pos_iff.mp (hb.symm ▸ NeZero.pos n)).isUnit.ne_zero
  let au : Eˣ := Units.mk0 a ha0
  let bu : Eˣ := Units.mk0 b hb0
  have hau : orderOf au = n := by simpa [← orderOf_units, au] using ha
  have hbu : orderOf bu = n := by simpa [← orderOf_units, bu] using hb
  have hgroups : Subgroup.zpowers au = Subgroup.zpowers bu :=
    IsCyclic.subgroup_eq_iff_card_eq.2 (by simp [Nat.card_zpowers, hau, hbu])
  have hmem : bu ∈ Subgroup.zpowers au := hgroups ▸ Subgroup.mem_zpowers bu
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 hmem
  change au ^ k = bu at hk
  have horder := orderOf_pow au (n := k)
  rw [hk, hau, hbu] at horder
  have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left n k)
  rw [← horder] at hmul
  have hgcd : Nat.gcd n k = 1 := by nlinarith [NeZero.pos n]
  refine ⟨k, (Nat.coprime_iff_gcd_eq_one.2 hgcd).symm, ?_⟩
  exact congrArg Units.val hk

/-- The choice of an element of exact order n in a finite ambient field
does not affect the root-code exceptional condition. -/
theorem nonstandardRootCode_same_order_iff {E : Type*} [Field E] [Finite E]
    (F : Subfield E) {a b : E} (ha : orderOf a = n) (hb : orderOf b = n) :
    nonstandardRootCode F n a ↔ nonstandardRootCode F n b := by
  obtain ⟨k, hk, rfl⟩ := exists_coprime_pow_eq_of_order_eq ha hb
  exact (nonstandardRootCode_pow_iff F ha hk).symm

#print axioms standardGroup_card
#print axioms standardGroup_eq_closure
#print axioms cyclicShift_eq_finRotate
#print axioms affinePerm_conjugate_standard_iff
#print axioms nonstandardRootCode_pow_iff
#print axioms nonstandardRootCode_same_order_iff

end NSDensity.Concrete
