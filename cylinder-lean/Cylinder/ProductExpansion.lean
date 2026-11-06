module

public import Cylinder.ProductResidueTransport
public import Cylinder.ProjectivePlaneForms

/-!
# The actual product expansion from the nonzero plane residues
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductExpansion

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveBalance Cylinder.ProductFrobenius Cylinder.ProductResidueTransport
open Cylinder.ProjectivePlaneForms
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def residueCoefficients {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (E : DualPoint p) : ZMod p :=
  if hE : E ∈ whitePoints p S then
    Classical.choose (exists_white_residue p hcard hS E hE)
  else 0

theorem residueCoefficients_spec {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    residueCoefficients p hcard hS E ≠ 0 ∧ planeForm p E ∣
      blackProduct p S - C (residueCoefficients p hcard hS E) * whiteProductExcept p S E := by
  simpa only [residueCoefficients, dite_eq_left hE] using
    Classical.choose_spec (exists_white_residue p hcard hS E hE)

def residueSum (S : Finset (Geometry.Point p)) (c : DualPoint p → ZMod p) : Form p :=
  ∑ E ∈ whitePoints p S, C (c E) * whiteProductExcept p S E

theorem planeForm_dvd_other_term (S : Finset (Geometry.Point p))
    (E H : DualPoint p) (hE : E ∈ whitePoints p S) (hEH : E ≠ H) :
    planeForm p E ∣ whiteProductExcept p S H :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hEH, hE⟩)

theorem planeForm_dvd_sub_residueSum {S : Finset (Geometry.Point p)}
    (c : DualPoint p → ZMod p) (E : DualPoint p) (hE : E ∈ whitePoints p S)
    (hres : planeForm p E ∣ blackProduct p S - C (c E) * whiteProductExcept p S E) :
    planeForm p E ∣ blackProduct p S - residueSum p S c := by
  have hother : planeForm p E ∣
      ∑ H ∈ (whitePoints p S).erase E, C (c H) * whiteProductExcept p S H := by
    apply Finset.dvd_sum
    intro H hH
    exact dvd_mul_of_dvd_right
      (planeForm_dvd_other_term p S E H hE (Ne.symm (Finset.mem_erase.mp hH).1)) _
  unfold residueSum
  rw [← Finset.sum_erase_add _ _ hE]
  convert dvd_sub hres hother using 1 <;> ring

theorem whiteProduct_dvd_sub_residueSum {S : Finset (Geometry.Point p)}
    (c : DualPoint p → ZMod p)
    (hres : ∀ E ∈ whitePoints p S,
      planeForm p E ∣ blackProduct p S - C (c E) * whiteProductExcept p S E) :
    whiteProduct p S ∣ blackProduct p S - residueSum p S c := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro E hE H hH hEH
    exact planeForm_isRelPrime p E H hEH
  · intro E hE
    exact planeForm_dvd_sub_residueSum p c E hE (hres E hE)

theorem residueSum_degree (S : Finset (Geometry.Point p)) (c : DualPoint p → ZMod p) :
    (residueSum p S c).totalDegree ≤ (whitePoints p S).card - 1 := by
  apply totalDegree_finsetSum_le
  intro E hE
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add, whiteProductExcept,
    white_erase_product_totalDegree p S E hE] using
    (le_refl ((whitePoints p S).card - 1))

theorem eq_residueSum_of_residues {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (c : DualPoint p → ZMod p)
    (hres : ∀ E ∈ whitePoints p S,
      planeForm p E ∣ blackProduct p S - C (c E) * whiteProductExcept p S E) :
    blackProduct p S = residueSum p S c := by
  apply sub_eq_zero.mp
  by_contra hzero
  have hdiv := whiteProduct_dvd_sub_residueSum p c hres
  have hle := totalDegree_le_of_dvd_of_isDomain hdiv hzero
  rw [whiteProduct_totalDegree] at hle
  have hdeg : (blackProduct p S - residueSum p S c).totalDegree ≤
      (whitePoints p S).card - 1 :=
    (totalDegree_sub _ _).trans (max_le (by rw [blackProduct_totalDegree p hcard hS])
      (residueSum_degree p S c))
  have hpos : 0 < (whitePoints p S).card := Finset.card_pos.mpr
    ⟨_, ProjectiveCover.infinity_mem_whitePoints p S⟩
  omega

/-- The manuscript's product identity with an actual everywhere nonzero white coefficient family. -/
theorem exists_nonzero_product_coefficients {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : DualPoint p → ZMod p, (∀ E ∈ whitePoints p S, c E ≠ 0) ∧
      blackProduct p S = ∑ E ∈ whitePoints p S, C (c E) * whiteProductExcept p S E := by
  refine ⟨residueCoefficients p hcard hS,
    fun E hE => (residueCoefficients_spec p hcard hS E hE).1, ?_⟩
  exact eq_residueSum_of_residues p hcard hS _
    (fun E hE => (residueCoefficients_spec p hcard hS E hE).2)

#print axioms residueCoefficients_spec
#print axioms exists_nonzero_product_coefficients

end Cylinder.ProductExpansion

end
