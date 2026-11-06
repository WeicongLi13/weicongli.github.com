module

public import Cylinder.ConicRootPairsGeometry

/-! Actual finite multiplicative subgroup cosets have zero first two
conic coordinate sums. Opposite-height blocks therefore sum to zero. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ConicCosetVectorSums

open Cylinder.ConicRootPairsGeometry

variable {K : Type*} [Field K]

theorem sum_subgroup_values_eq_zero (H : Subgroup Kˣ) [Fintype H]
    (hcard : 1 < Fintype.card H) : (∑ h : H, (h.val : K)) = 0 := by
  have hex : ∃ g : H, g ≠ 1 := by
    by_contra! h
    let _ : Unique H := { default := 1, uniq := h }
    have hs := Fintype.card_unique (α := H)
    omega
  obtain ⟨g, hg⟩ := hex
  have hgn : (g.val : K) ≠ 1 := by
    intro h
    exact hg (Subtype.ext (Units.ext h))
  have hshift : (g.val : K) * (∑ h : H, (h.val : K)) = ∑ h : H, (h.val : K) := by
    calc
      _ = ∑ h : H, (g.val : K) * (h.val : K) := Finset.mul_sum _ _ _
      _ = ∑ h : H, ((g * h).val : K) := rfl
      _ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h : H => (h.val : K))
  have hz : ((g.val : K) - 1) * (∑ h : H, (h.val : K)) = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hgn)

theorem sum_subgroup_inverse_values_eq_zero (H : Subgroup Kˣ) [Fintype H]
    (hcard : 1 < Fintype.card H) : (∑ h : H, (h.val : K)⁻¹) = 0 := by
  have hsum := Equiv.sum_comp (Equiv.inv H) (fun h : H => (h.val : K))
  change (∑ h : H, ((h⁻¹).val : K)) = ∑ h : H, (h.val : K) at hsum
  have heq : (∑ h : H, (h.val : K)⁻¹) = ∑ h : H, (h.val : K) := by
    simpa only [Subgroup.coe_inv, Units.val_inv_eq_inv_val] using hsum
  rw [heq]
  exact sum_subgroup_values_eq_zero H hcard

theorem hyperbola_coset_vector_sum (H : Subgroup Kˣ) [Fintype H]
    (hcard : 1 < Fintype.card H) (u : Kˣ) (c : K) :
    (∑ h : H, c • hyperbolaVector (u * h.val)) =
      ![0, 0, (Fintype.card H : K) * c] := by
  funext j
  fin_cases j
  · simp only [Finset.sum_apply]
    change (∑ h : H, c * ((u : K) * (h.val : K))) = 0
    have heq : (∑ h : H, c * ((u : K) * (h.val : K))) =
        (c * (u : K)) * (∑ h : H, (h.val : K)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    rw [heq, sum_subgroup_values_eq_zero H hcard, mul_zero]
  · simp only [Finset.sum_apply]
    change (∑ h : H, c * ((u : K) * (h.val : K))⁻¹) = 0
    have heq : (∑ h : H, c * ((u : K) * (h.val : K))⁻¹) =
        (c * (u : K)⁻¹) * (∑ h : H, (h.val : K)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [mul_inv_rev]
      ring
    rw [heq, sum_subgroup_inverse_values_eq_zero H hcard, mul_zero]
  · simp [Finset.sum_apply, hyperbolaVector, smul_eq_mul]

theorem opposite_hyperbola_blocks_sum_zero (H : Subgroup Kˣ) [Fintype H]
    (hcard : 1 < Fintype.card H) (u v : Kˣ) (c : K) :
    (∑ h : H, c • hyperbolaVector (u * h.val)) +
      (∑ h : H, (-c) • hyperbolaVector (v * h.val)) = 0 := by
  rw [hyperbola_coset_vector_sum H hcard u c, hyperbola_coset_vector_sum H hcard v (-c)]
  funext j
  fin_cases j <;> simp

end Cylinder.ConicCosetVectorSums

end
