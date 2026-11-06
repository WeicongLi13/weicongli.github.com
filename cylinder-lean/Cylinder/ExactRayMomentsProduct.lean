module

public import Cylinder.ExactRayMomentsCoefficient
public import Cylinder.ExactRayMomentsHighest
public import Cylinder.ExactRayMomentsMultiplicity

/-!
# Exact moments from actual normalized white and black products

The black numerator is an actual product with the center factor `T^w`.
Line balance is expressed as equality of the actual factor counts. Prime
numerator and denominator multiplicities are proved from these products;
neither low moment vanishing nor the highest moment nonvanishing is assumed.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsProduct
open Cylinder.ExactRayMomentsLow Cylinder.ExactRayMomentsCoefficient
open Cylinder.ExactRayMomentsMultiplicity
variable {K R E I J : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Fintype E] [Fintype I] [Fintype J]

def blackPolynomial (dir : J → I) (a : I → R) (scale time : J → K) (weight : J → ℕ) (w : ℕ) :
    Polynomial R := Polynomial.X ^ w *
      ∏ j, actualFactor (algebraMap K R (scale j) * a (dir j)) (time j) ^ weight j

omit [IsDomain R] [Fintype I] in
theorem blackPolynomial_leading_coefficient (dir : J → I) (a : I → R)
    (scale time : J → K) (weight : J → ℕ) (w : ℕ) :
    (blackPolynomial dir a scale time weight w).coeff w = directionProduct dir a scale weight := by
  let Q : Polynomial R := ∏ j, actualFactor (algebraMap K R (scale j) * a (dir j)) (time j) ^ weight j
  have hshift := Polynomial.coeff_X_pow_mul Q w 0
  change (Polynomial.X ^ w * Q).coeff w = _
  simp only [Nat.zero_add] at hshift
  rw [hshift]
  change Polynomial.constantCoeff Q = _
  dsimp only [Q]
  rw [map_prod]
  simp only [map_pow]
  simp [actualFactor, directionProduct]

omit [IsDomain R] [Fintype I] in
theorem whitePolynomial_constant (dir : E → I) (a : I → R) (time : E → K) :
    (actualDenominator dir a time).coeff 0 = directionProduct dir a (fun _ => (1 : K)) (fun _ => 1) := by
  rw [actualDenominator_constant]
  simp [directionProduct]

theorem normalized_balanced_product_exact_moments
    (dir : E → I) (blackDir : J → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (c time : E → K) (scale blackTime : J → K) (hscale : ∀ j, scale j ≠ 0)
    (weight : J → ℕ) (w : ℕ) (P : Polynomial R)
    (hprod : P = actualNumerator dir a c time)
    (hblack : P = blackPolynomial blackDir a scale blackTime weight w)
    (hbalance : ∀ i, directionExponent dir (fun _ => 1) i =
      w + 1 + directionExponent blackDir weight i) :
    (∀ j, j < w → ∀ i, moment dir c time i j = 0) ∧
      ∀ i, moment dir c time i w ≠ 0 := by
  have horder : Polynomial.X ^ w ∣ P := by
    rw [hblack]
    exact dvd_mul_right _ _
  refine ⟨fun j hj => normalized_product_low_moments dir a ha hsep c time P hprod w horder j hj, ?_⟩
  let A := P.coeff w
  let B := (actualDenominator dir a time).coeff 0
  have hA : A = directionProduct blackDir a scale weight := by
    dsimp only [A]
    rw [hblack, blackPolynomial_leading_coefficient]
  have hB : B = directionProduct dir a (fun _ => (1 : K)) (fun _ => 1) :=
    whitePolynomial_constant dir a time
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact directionProduct_nonzero dir a (fun i => (ha i).ne_zero) _ (fun _ => one_ne_zero) _
  have hpoles := balanced_direction_products_have_poles dir blackDir a ha hsep scale hscale weight w hbalance
  have hden (i : I) : a i ^ directionExponent dir (fun _ => 1) i ∣ B := by
    rw [hB]
    exact (hpoles i).1
  have hnum (i : I) : ¬a i ^ directionExponent dir (fun _ => 1) i ∣ A := by
    rw [hA]
    exact (hpoles i).2
  have hquot := normalized_product_first_coefficient dir a (fun i => (ha i).ne_zero) c time P hprod w horder
  exact Cylinder.ExactRayMomentsHighest.actual_poles_force_coefficients_nonzero
    (F := FractionRing R) a ha hsep (fun i => moment dir c time i w) (w + 1)
    A B ((-1 : R) ^ w) hB0 (directionExponent dir (fun _ => 1)) hden hnum hquot

end Cylinder.ExactRayMomentsProduct
end
