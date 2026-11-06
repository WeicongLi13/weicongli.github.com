module

public import Cylinder.FiniteCosetAlgebra

/-! Minimal product sets, without an identity normalization hypothesis,
are actual left and right cosets of the same finite subgroup. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FiniteCosetNormalization

open Cylinder.FiniteCosetAlgebra

variable {G : Type*} [Group G]

@[to_additive normalizeAddLeft]
def normalizeLeft (A : Finset G) (a : G) : Finset G := A.image (fun x => a⁻¹ * x)

@[to_additive normalizeAddRight]
def normalizeRight (B : Finset G) (b : G) : Finset G := B.image (fun y => y * b⁻¹)

@[to_additive normalizeAddLeft_card]
theorem normalizeLeft_card (A : Finset G) (a : G) : (normalizeLeft A a).card = A.card :=
  Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

@[to_additive normalizeAddRight_card]
theorem normalizeRight_card (B : Finset G) (b : G) : (normalizeRight B b).card = B.card :=
  Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel h)

@[to_additive normalized_sums_eq]
theorem normalized_products_eq (A B : Finset G) (a b : G) :
    products (normalizeLeft A a) (normalizeRight B b) =
      (products A B).image (fun x => a⁻¹ * x * b⁻¹) := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨r * s,
      Finset.mem_image.mpr ⟨(r, s), Finset.mem_product.mpr ⟨hr, hs⟩, rfl⟩, by simp only [mul_assoc]⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp hrs
    exact Finset.mem_image.mpr ⟨(a⁻¹ * r, s * b⁻¹),
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩,
        Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩, by simp only [mul_assoc]⟩

@[to_additive normalizeAddLeft_mem]
theorem normalizeLeft_mem (A : Finset G) (a x : G) : a⁻¹ * x ∈ normalizeLeft A a ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp h
    exact (mul_left_cancel heq) ▸ hy
  · intro h
    exact Finset.mem_image.mpr ⟨x, h, rfl⟩

@[to_additive normalizeAddRight_mem]
theorem normalizeRight_mem (B : Finset G) (b y : G) : y * b⁻¹ ∈ normalizeRight B b ↔ y ∈ B := by
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
    exact (mul_right_cancel heq) ▸ hx
  · intro h
    exact Finset.mem_image.mpr ⟨y, h, rfl⟩

@[to_additive minimal_sums_are_cosets]
theorem minimal_products_are_cosets (A B : Finset G) (a b : G) (ha : a ∈ A) (hb : b ∈ B)
    (hcardA : (products A B).card = A.card) (hcardB : (products A B).card = B.card) :
    ∃ H : Subgroup G, Finite H ∧ Nat.card H = A.card ∧
      (∀ x, x ∈ A ↔ a⁻¹ * x ∈ H) ∧ (∀ y, y ∈ B ↔ y * b⁻¹ ∈ H) := by
  have hleft : 1 ∈ normalizeLeft A a := Finset.mem_image.mpr ⟨a, ha, inv_mul_cancel a⟩
  have hright : 1 ∈ normalizeRight B b := Finset.mem_image.mpr ⟨b, hb, mul_inv_cancel b⟩
  have hc : (products (normalizeLeft A a) (normalizeRight B b)).card = (products A B).card := by
    rw [normalized_products_eq, Finset.card_image_of_injective _
      (fun _ _ h => mul_left_cancel (mul_right_cancel h))]
  obtain ⟨H, hHleft, hHright⟩ := normalized_product_subgroup (normalizeLeft A a)
    (normalizeRight B b) hleft hright
    (by rw [hc, normalizeLeft_card, hcardA]) (by rw [hc, normalizeRight_card, hcardB])
  let e : H ≃ normalizeLeft A a := Equiv.subtypeEquivRight hHleft
  have hfinite : Finite H := Finite.of_equiv (normalizeLeft A a) e.symm
  have hcard : Nat.card H = A.card := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, normalizeLeft_card]
  refine ⟨H, hfinite, hcard, fun x => ?_, fun y => ?_⟩
  · rw [hHleft, normalizeLeft_mem]
  · rw [hHright, normalizeRight_mem]

end Cylinder.FiniteCosetNormalization

end
