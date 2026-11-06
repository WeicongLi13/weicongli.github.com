module

public import Cylinder.ProductFrobeniusRelation

/-!
# Rechoosing the nonzero rational plane equations

All nonzero rescalings of the actual plane forms have the product
expansion and the degree-`p-2` Frobenius relation. The new coefficient
family includes the global product scale and each local plane scale.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductRescaling

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductResidueTransport Cylinder.ProductExpansion
open Cylinder.ProductFrobeniusRelation
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def scaledPlaneForm (a : DualPoint p → ZMod p) (H : DualPoint p) : Form p :=
  C (a H) * planeForm p H

def whiteScalar (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p) : ZMod p :=
  ∏ H ∈ whitePoints p S, a H

def blackScalar (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p) : ZMod p :=
  ∏ H ∈ blackPoints p S, a H ^ weight p S H

def erasedScalar (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p)
    (E : DualPoint p) : ZMod p := ∏ H ∈ (whitePoints p S).erase E, a H

theorem scaled_product (T : Finset (DualPoint p)) (a : DualPoint p → ZMod p)
    (m : DualPoint p → ℕ) :
    (∏ H ∈ T, scaledPlaneForm p a H ^ m H) =
      C (∏ H ∈ T, a H ^ m H) * ∏ H ∈ T, planeForm p H ^ m H := by
  simp only [scaledPlaneForm, mul_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod]

theorem scaled_white_erased_product (S : Finset (Geometry.Point p))
    (a : DualPoint p → ZMod p) (E : DualPoint p) :
    (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) =
      C (erasedScalar p S a E) * whiteProductExcept p S E := by
  simpa only [pow_one, erasedScalar, whiteProductExcept] using
    scaled_product p ((whitePoints p S).erase E) a (fun _ => 1)

theorem erasedScalar_factor (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p)
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    a E * erasedScalar p S a E = whiteScalar p S a := Finset.mul_prod_erase _ _ hE

theorem whiteScalar_ne_zero (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p)
    (ha : ∀ H ∈ whitePoints p S, a H ≠ 0) : whiteScalar p S a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr ha

theorem blackScalar_ne_zero (S : Finset (Geometry.Point p)) (a : DualPoint p → ZMod p)
    (ha : ∀ H ∈ blackPoints p S, a H ≠ 0) : blackScalar p S a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun H hH => pow_ne_zero _ (ha H hH))

theorem scaled_residue_term (S : Finset (Geometry.Point p))
    (a c : DualPoint p → ZMod p) (hwhite : ∀ H ∈ whitePoints p S, a H ≠ 0)
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    C ((blackScalar p S a / whiteScalar p S a) * a E * c E) *
      (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) =
      C (blackScalar p S a) * (C (c E) * whiteProductExcept p S E) := by
  rw [scaled_white_erased_product, ← mul_assoc, ← map_mul]
  have he : ((blackScalar p S a / whiteScalar p S a) * a E * c E) *
      erasedScalar p S a E = blackScalar p S a * c E := by
    calc
      _ = ((blackScalar p S a / whiteScalar p S a) *
        (a E * erasedScalar p S a E)) * c E := by ring
      _ = blackScalar p S a * c E := by
        rw [erasedScalar_factor p S a E hE,
          div_mul_cancel₀ _ (whiteScalar_ne_zero p S a hwhite)]
  rw [he, map_mul, mul_assoc]

theorem scalar_fermat_shift {a : ZMod p} (ha : a ≠ 0) : a * a ^ (p - 2) = 1 := by
  rw [← pow_succ']
  have hp := (Fact.out : p.Prime).two_le
  convert ZMod.pow_card_sub_one_eq_one ha using 1 <;> congr 1 <;> omega

theorem scaled_power_term (a c : DualPoint p → ZMod p) (t : ZMod p)
    (E : DualPoint p) (ha : a E ≠ 0) :
    C (t * a E * c E) * scaledPlaneForm p a E ^ (p - 2) =
      C t * (C (c E) * planeForm p E ^ (p - 2)) := by
  rw [scaledPlaneForm, mul_pow, ← map_pow]
  calc
    _ = C (t * c E * (a E * a E ^ (p - 2))) * planeForm p E ^ (p - 2) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [scalar_fermat_shift p ha]; simp only [mul_one, map_mul]; ring

theorem exists_rescaled_product_and_frobenius_coefficients {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (a : DualPoint p → ZMod p)
    (hwhite : ∀ H ∈ whitePoints p S, a H ≠ 0)
    (hblack : ∀ H ∈ blackPoints p S, a H ≠ 0) :
    ∃ c : DualPoint p → ZMod p, (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
        (∑ E ∈ whitePoints p S, C (c E) *
          (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)) ∧
      (∑ E ∈ whitePoints p S, C (c E) * scaledPlaneForm p a E ^ (p - 2)) = 0 := by
  obtain ⟨c, hc, hprod, hpower⟩ := exists_nonzero_product_and_frobenius_coefficients p hcard hS
  let t := blackScalar p S a / whiteScalar p S a
  have ht : t ≠ 0 := div_ne_zero (blackScalar_ne_zero p S a hblack)
    (whiteScalar_ne_zero p S a hwhite)
  refine ⟨fun E => t * a E * c E,
    fun E hE => mul_ne_zero (mul_ne_zero ht (hwhite E hE)) (hc E hE), ?_, ?_⟩
  · rw [scaled_product, show (∏ H ∈ blackPoints p S, a H ^ weight p S H) =
      blackScalar p S a from rfl, show (∏ H ∈ blackPoints p S, planeForm p H ^ weight p S H) =
      blackProduct p S from rfl, hprod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    exact (scaled_residue_term p S a c hwhite E hE).symm
  · have hsum : (∑ E ∈ whitePoints p S,
        C (t * a E * c E) * scaledPlaneForm p a E ^ (p - 2)) =
        C t * ∑ E ∈ whitePoints p S, C (c E) * planeForm p E ^ (p - 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      exact scaled_power_term p a c t E (hwhite E hE)
    rw [hsum, hpower, mul_zero]

/-- Every nonzero functional representing `H` is an allowed nonzero rescaling. -/
theorem representative_functional_scaled (H : DualPoint p)
    (f : Module.Dual (ZMod p) (Vector p)) (hf : f ≠ 0)
    (hrep : Projectivization.mk (ZMod p) f hf = H) :
    ∃ a : ZMod p, a ≠ 0 ∧ ProductCoordinates.functionalForm p f = C a * planeForm p H := by
  have heq : Projectivization.mk (ZMod p) f hf =
      Projectivization.mk (ZMod p) H.rep H.rep_nonzero := hrep.trans (Projectivization.mk_rep H).symm
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff (ZMod p) f H.rep hf H.rep_nonzero).mp heq
  refine ⟨a, a.ne_zero, ?_⟩
  rw [← ha, Units.smul_def, ProductCoordinates.functionalForm_smul]
  rfl

#print axioms exists_rescaled_product_and_frobenius_coefficients
#print axioms representative_functional_scaled

end Cylinder.ProductRescaling

end
