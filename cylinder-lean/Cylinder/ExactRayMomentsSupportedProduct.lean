module

public import Cylinder.ExactRayMomentsProduct

/-!
# Exact moments on the actual support of the white product

All black directions are retained. Factor balance is required only in the
directions with a white factor; the corresponding highest moments are
nonzero. Black factors in other directions remain in the actual numerator.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsSupportedProduct
open Cylinder.ExactRayMomentsLow Cylinder.ExactRayMomentsCoefficient
open Cylinder.ExactRayMomentsMultiplicity Cylinder.ExactRayMomentsProduct
variable {K R F E I J : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable [Fintype E] [Fintype I] [Fintype J]

theorem coefficient_nonzero_of_actual_pole
    (a : I → R) (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (m : I → K) (n : ℕ) (A B u : R) (hB0 : B ≠ 0) (i : I) (q : ℕ)
    (hden : a i ^ q ∣ B) (hnum : ¬a i ^ q ∣ A)
    (hquot : algebraMap R F A / algebraMap R F B = algebraMap R F u *
      ∑ k, algebraMap R F (algebraMap K R (m k)) / algebraMap R F (a k) ^ n) : m i ≠ 0 := by
  intro hmi
  obtain ⟨D, Q, hnot, hD0, hregular⟩ :=
    Cylinder.ExactRayMomentsHighest.fraction_sum_regular_of_coefficient_zero (F := F) a ha hsep m n i hmi
  have hBmap : algebraMap R F B ≠ 0 := by
    intro hz
    exact hB0 (IsFractionRing.injective R F (by simpa using hz))
  have hDmap : algebraMap R F D ≠ 0 := by
    intro hz
    exact hD0 (IsFractionRing.injective R F (by simpa using hz))
  rw [hregular, ← mul_div_assoc, ← map_mul] at hquot
  have heq := (div_eq_div_iff hBmap hDmap).mp hquot
  have heqR : A * D = (u * Q) * B := by
    apply IsFractionRing.injective R F
    simpa only [map_mul] using heq
  have hdiv : a i ^ q ∣ A * D := by
    rw [heqR]
    exact dvd_mul_of_dvd_right hden _
  exact hnum ((ha i).pow_dvd_of_dvd_mul_right q hnot hdiv)

omit [Fintype I] in
theorem direction_products_pole_at
    (dir : E → I) (blackDir : J → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (scale : J → K) (hscale : ∀ j, scale j ≠ 0) (weight : J → ℕ) (w : ℕ) (i : I)
    (hbalance : directionExponent dir (fun _ => 1) i = w + 1 + directionExponent blackDir weight i) :
    a i ^ directionExponent dir (fun _ => 1) i ∣
        directionProduct dir a (fun _ => (1 : K)) (fun _ => 1) ∧
      ¬a i ^ directionExponent dir (fun _ => 1) i ∣ directionProduct blackDir a scale weight := by
  have hwhite := directionProduct_emultiplicity dir a ha hsep (fun _ => (1 : K))
    (fun _ => one_ne_zero) (fun _ => 1) i
  have hblack := directionProduct_emultiplicity blackDir a ha hsep scale hscale weight i
  constructor
  · apply pow_dvd_of_le_emultiplicity
    rw [hwhite]
  · apply not_pow_dvd_of_emultiplicity_lt
    rw [hblack]
    have hlt : directionExponent blackDir weight i < directionExponent dir (fun _ => 1) i := by
      rw [hbalance]
      omega
    exact_mod_cast hlt

theorem supported_balanced_product_exact_moments
    (dir : E → I) (blackDir : J → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (c time : E → K) (scale blackTime : J → K) (hscale : ∀ j, scale j ≠ 0)
    (weight : J → ℕ) (w : ℕ) (P : Polynomial R)
    (hprod : P = actualNumerator dir a c time)
    (hblack : P = blackPolynomial blackDir a scale blackTime weight w)
    (hbalance : ∀ i, 0 < directionExponent dir (fun _ => 1) i →
      directionExponent dir (fun _ => 1) i = w + 1 + directionExponent blackDir weight i) :
    (∀ j, j < w → ∀ i, moment dir c time i j = 0) ∧
      ∀ i, 0 < directionExponent dir (fun _ => 1) i → moment dir c time i w ≠ 0 := by
  have horder : Polynomial.X ^ w ∣ P := by
    rw [hblack]
    exact dvd_mul_right _ _
  refine ⟨fun j hj => normalized_product_low_moments dir a ha hsep c time P hprod w horder j hj, ?_⟩
  intro i hi
  let A := P.coeff w
  let B := (actualDenominator dir a time).coeff 0
  have hA : A = directionProduct blackDir a scale weight := by
    dsimp only [A]
    rw [hblack, blackPolynomial_leading_coefficient]
  have hB : B = directionProduct dir a (fun _ => (1 : K)) (fun _ => 1) :=
    whitePolynomial_constant dir a time
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact directionProduct_nonzero dir a (fun k => (ha k).ne_zero) _ (fun _ => one_ne_zero) _
  have hpole := direction_products_pole_at dir blackDir a ha hsep scale hscale weight w i (hbalance i hi)
  have hden : a i ^ directionExponent dir (fun _ => 1) i ∣ B := by
    rw [hB]
    exact hpole.1
  have hnum : ¬a i ^ directionExponent dir (fun _ => 1) i ∣ A := by
    rw [hA]
    exact hpole.2
  have hquot := normalized_product_first_coefficient dir a (fun k => (ha k).ne_zero) c time P hprod w horder
  exact coefficient_nonzero_of_actual_pole (F := FractionRing R) a ha hsep
    (fun k => moment dir c time k w) (w + 1) A B ((-1 : R) ^ w) hB0 i
    (directionExponent dir (fun _ => 1) i) hden hnum hquot

end Cylinder.ExactRayMomentsSupportedProduct
end
