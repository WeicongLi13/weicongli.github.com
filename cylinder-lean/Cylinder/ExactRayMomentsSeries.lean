module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Actual residue products and their moment series

The reciprocal series is constructed coefficient by coefficient and proved to
invert the actual linear factor. The product-residue identity then implies
vanishing of all low series coefficients; these are the actual moment sums.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsSeries
variable {F E : Type*} [Field F] [Fintype E]

def reciprocalSeries (a t : F) : PowerSeries F :=
  PowerSeries.mk (fun j => a⁻¹ * (-t / a) ^ j)

theorem reciprocalSeries_coefficient (a t : F) (j : ℕ) :
    PowerSeries.coeff j (reciprocalSeries a t) = (-1) ^ j * t ^ j / a ^ (j + 1) := by
  rw [reciprocalSeries, PowerSeries.coeff_mk, div_pow, neg_pow]
  simp only [div_eq_mul_inv, pow_succ, mul_inv_rev]
  ring

theorem reciprocalSeries_inverse (a t : F) (ha : a ≠ 0) :
    (PowerSeries.C a + PowerSeries.C t * PowerSeries.X) * reciprocalSeries a t = 1 := by
  rw [add_mul, mul_assoc]
  apply PowerSeries.ext
  intro j
  cases j with
  | zero => simp [reciprocalSeries, ha]
  | succ j =>
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      reciprocalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false,
      pow_succ]
    field_simp [ha]
    ring

def linearFactor (a t : F) : Polynomial F := Polynomial.C a + Polynomial.C t * Polynomial.X

def denominator (a t : E → F) : Polynomial F := ∏ e, linearFactor (a e) (t e)

def residueNumerator (a t c : E → F) : Polynomial F :=
  ∑ e, Polynomial.C (c e) * ∏ f ∈ Finset.univ.erase e, linearFactor (a f) (t f)

def residueSeries (a t c : E → F) : PowerSeries F :=
  ∑ e, PowerSeries.C (c e) * reciprocalSeries (a e) (t e)

theorem residueSeries_product (a t c : E → F) (ha : ∀ e, a e ≠ 0) :
    residueSeries a t c * (denominator a t : PowerSeries F) = residueNumerator a t c := by
  let ι : Polynomial F →+* PowerSeries F := Polynomial.coeToPowerSeries.ringHom
  change residueSeries a t c * ι (denominator a t) = ι (residueNumerator a t c)
  rw [residueSeries, residueNumerator, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  have hfactor : denominator a t = linearFactor (a e) (t e) *
      ∏ f ∈ Finset.univ.erase e, linearFactor (a f) (t f) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ e)).symm
  rw [hfactor, map_mul, map_mul]
  have hL : ι (linearFactor (a e) (t e)) = PowerSeries.C (a e) + PowerSeries.C (t e) * PowerSeries.X := by
    simp [ι, linearFactor]
  have hC : ι (Polynomial.C (c e)) = PowerSeries.C (c e) := Polynomial.coe_C _
  rw [hL, hC]
  calc
    _ = PowerSeries.C (c e) *
        (((PowerSeries.C (a e) + PowerSeries.C (t e) * PowerSeries.X) * reciprocalSeries (a e) (t e)) *
          ι (∏ f ∈ Finset.univ.erase e, linearFactor (a f) (t f))) := by ring
    _ = _ := by rw [reciprocalSeries_inverse _ _ (ha e), one_mul]

theorem denominator_constant_ne_zero (a t : E → F) (ha : ∀ e, a e ≠ 0) :
    PowerSeries.constantCoeff (denominator a t : PowerSeries F) ≠ 0 := by
  let ι : Polynomial F →+* PowerSeries F := Polynomial.coeToPowerSeries.ringHom
  change (PowerSeries.constantCoeff.comp ι) (denominator a t) ≠ 0
  rw [denominator, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  simpa [ι, linearFactor] using ha e

theorem residueSeries_coefficient (a t c : E → F) (j : ℕ) :
    PowerSeries.coeff j (residueSeries a t c) =
      (-1) ^ j * ∑ e, c e * t e ^ j / a e ^ (j + 1) := by
  simp only [residueSeries, map_sum, PowerSeries.coeff_C_mul, reciprocalSeries_coefficient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem product_low_moment_sum (a t c : E → F) (ha : ∀ e, a e ≠ 0)
    (P : Polynomial F) (hprod : P = residueNumerator a t c) (w : ℕ)
    (horder : Polynomial.X ^ w ∣ P) (j : ℕ) (hj : j < w) :
    (∑ e, c e * t e ^ j / a e ^ (j + 1)) = 0 := by
  let ι : Polynomial F →+* PowerSeries F := Polynomial.coeToPowerSeries.ringHom
  have hN0 := denominator_constant_ne_zero a t ha
  have hseries : residueSeries a t c = (P : PowerSeries F) * (denominator a t : PowerSeries F)⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq hN0).mpr
    rw [residueSeries_product a t c ha, hprod]
  have hX : PowerSeries.X ^ w ∣ (P : PowerSeries F) := by
    have h := map_dvd ι horder
    simpa [ι] using h
  have hdiv : PowerSeries.X ^ w ∣ residueSeries a t c := by
    rw [hseries]
    exact dvd_mul_of_dvd_left hX _
  have hz := (PowerSeries.X_pow_dvd_iff.mp hdiv) j hj
  rw [residueSeries_coefficient] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero))

theorem product_first_moment_sum (a t c : E → F) (ha : ∀ e, a e ≠ 0)
    (P : Polynomial F) (hprod : P = residueNumerator a t c) (w : ℕ)
    (horder : Polynomial.X ^ w ∣ P) :
    (-1) ^ w * (∑ e, c e * t e ^ w / a e ^ (w + 1)) =
      P.coeff w / (denominator a t).coeff 0 := by
  have hN0 := denominator_constant_ne_zero a t ha
  have hseries : residueSeries a t c = (P : PowerSeries F) * (denominator a t : PowerSeries F)⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq hN0).mpr
    rw [residueSeries_product a t c ha, hprod]
  obtain ⟨Q, hQ⟩ := horder
  have hPs : (P : PowerSeries F) = PowerSeries.X ^ w * (Q : PowerSeries F) := by
    rw [hQ, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  have hSs : residueSeries a t c = PowerSeries.X ^ w *
      ((Q : PowerSeries F) * (denominator a t : PowerSeries F)⁻¹) := by
    rw [hseries, hPs, mul_assoc]
  have hPc : P.coeff w = Q.coeff 0 := by
    have h := congrArg (PowerSeries.coeff w) hPs
    have hshift := PowerSeries.coeff_X_pow_mul (Q : PowerSeries F) w 0
    simpa only [Nat.zero_add, Polynomial.coeff_coe] using h.trans (by simpa using hshift)
  have hSc : PowerSeries.coeff w (residueSeries a t c) =
      Q.coeff 0 * ((denominator a t).coeff 0)⁻¹ := by
    rw [hSs]
    have hshift := PowerSeries.coeff_X_pow_mul
      ((Q : PowerSeries F) * (denominator a t : PowerSeries F)⁻¹) w 0
    simp only [Nat.zero_add] at hshift
    rw [hshift]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe]
  rw [← residueSeries_coefficient, hSc, hPc, div_eq_mul_inv]

end Cylinder.ExactRayMomentsSeries
end
