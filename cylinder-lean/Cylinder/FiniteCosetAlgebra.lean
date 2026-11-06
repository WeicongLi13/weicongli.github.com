module

public import Cylinder.BMMMatchingParity
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! The finite product-set argument behind conic subgroup cosets. Equal
minimal product cardinality, after normalization at the identity, gives
an actual subgroup rather than an assumed closure property. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FiniteCosetAlgebra

variable {G : Type*} [Group G]

@[to_additive sums]
def products (A B : Finset G) : Finset G := (A ×ˢ B).image (fun x => x.1 * x.2)

@[to_additive left_subset_sums]
theorem left_subset_products (A B : Finset G) (hB : 1 ∈ B) : A ⊆ products A B := by
  intro a ha
  exact Finset.mem_image.mpr ⟨(a, 1), Finset.mem_product.mpr ⟨ha, hB⟩, mul_one a⟩

@[to_additive right_subset_sums]
theorem right_subset_products (A B : Finset G) (hA : 1 ∈ A) : B ⊆ products A B := by
  intro b hb
  exact Finset.mem_image.mpr ⟨(1, b), Finset.mem_product.mpr ⟨hA, hb⟩, one_mul b⟩

@[to_additive normalized_sum_sets_equal]
theorem normalized_sets_equal (A B : Finset G) (hA : 1 ∈ A) (hB : 1 ∈ B)
    (hcardA : (products A B).card = A.card) (hcardB : (products A B).card = B.card) :
    A = B ∧ products A B = A := by
  have ha : A = products A B := Finset.eq_of_subset_of_card_le
    (left_subset_products A B hB) (by omega)
  have hb : B = products A B := Finset.eq_of_subset_of_card_le
    (right_subset_products A B hA) (by omega)
  exact ⟨ha.trans hb.symm, ha.symm⟩

@[to_additive finite_additive_closure_neg]
theorem finite_multiplicative_closure_inv (S : Finset G) (hS : 1 ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : ∀ a ∈ S, a⁻¹ ∈ S := by
  intro a ha
  let f : S → S := fun b => ⟨a * b.val, hmul a ha b.val b.property⟩
  have hinj : Function.Injective f := by
    intro b c h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hinj) (⟨1, hS⟩ : S)
  have hv : a * b.val = 1 := congrArg Subtype.val hb
  have heq : b.val = a⁻¹ := by
    calc
      b.val = a⁻¹ * (a * b.val) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = a⁻¹ := by rw [hv, mul_one]
  exact heq ▸ b.property

@[to_additive normalized_sum_addSubgroup]
theorem normalized_product_subgroup (A B : Finset G) (hA : 1 ∈ A) (hB : 1 ∈ B)
    (hcardA : (products A B).card = A.card) (hcardB : (products A B).card = B.card) :
    ∃ H : Subgroup G, (∀ a, a ∈ H ↔ a ∈ A) ∧ (∀ b, b ∈ H ↔ b ∈ B) := by
  obtain ⟨hab, hp⟩ := normalized_sets_equal A B hA hB hcardA hcardB
  have hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb
    rw [← hp]
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hab ▸ hb⟩, rfl⟩
  let H : Subgroup G := {
    carrier := (A : Set G)
    one_mem' := hA
    mul_mem' := fun {a b} ha hb => hmul a ha b hb
    inv_mem' := fun {a} ha => finite_multiplicative_closure_inv A hA hmul a ha }
  refine ⟨H, fun _ => Iff.rfl, fun b => ?_⟩
  change b ∈ A ↔ b ∈ B
  rw [hab]

end Cylinder.FiniteCosetAlgebra

end
