module

public import Cylinder.TripleCoordinateLocalization
public import Cylinder.CurvePolarLocal

/-! Literal coordinate fractions from every chart map into the same
actual affine torus localization. Cross multiplication in the original
polynomial ring gives equality there, without a denominator-value
assumption. This is the common target for comparing chart restrictions. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CommonTorusFractions

open MvPolynomial Cylinder.CoordinateLaurentLocalization
open Cylinder.CurvePolarLocal

set_option autoImplicit false

variable (K : Type*) [Field K]

abbrev TorusRing := TripleCoordinateLocalization.productLocalization K

def polynomialMap : PlaneRing K →+* TorusRing K :=
  (algebraMap (AffineRing K) (TorusRing K)).comp dehomogenize

theorem coordinate_unit (i : Option (Fin 2)) : IsUnit (polynomialMap K (X i)) := by
  cases i with
  | none => simp [polynomialMap]
  | some i =>
    simp only [polynomialMap, RingHom.comp_apply, dehomogenize_X_some]
    fin_cases i
    · exact IsLocalization.Away.isUnit_of_dvd
        (S := TorusRing K) ((X 0 : AffineRing K) * X 1) (dvd_mul_right _ _)
    · exact IsLocalization.Away.isUnit_of_dvd
        (S := TorusRing K) ((X 0 : AffineRing K) * X 1) (dvd_mul_left _ _)

def coordinateMap (i : Option (Fin 2)) : Localization.Away (X i : PlaneRing K) →+* TorusRing K :=
  IsLocalization.Away.lift (X i) (coordinate_unit K i)

theorem coordinateMap_algebraMap (i : Option (Fin 2)) (H : PlaneRing K) :
    coordinateMap K i (algebraMap (PlaneRing K) (Localization.Away (X i : PlaneRing K)) H) =
      polynomialMap K H :=
  IsLocalization.Away.lift_eq (X i) (coordinate_unit K i) H

def coordinateFraction (i : Option (Fin 2)) (n : ℕ) (H : PlaneRing K) : TorusRing K :=
  coordinateMap K i
    (IsLocalization.mk' (M := Submonoid.powers (X i : PlaneRing K))
      (Localization.Away (X i : PlaneRing K)) H ⟨X i ^ n, n, rfl⟩)

theorem coordinateFraction_clear (i : Option (Fin 2)) (n : ℕ) (H : PlaneRing K) :
    coordinateFraction K i n H * polynomialMap K (X i) ^ n = polynomialMap K H := by
  have h := congrArg (coordinateMap K i)
    (IsLocalization.mk'_spec (M := Submonoid.powers (X i : PlaneRing K))
      (Localization.Away (X i : PlaneRing K)) H ⟨X i ^ n, n, rfl⟩)
  simpa only [coordinateFraction, map_mul, coordinateMap_algebraMap, map_pow] using h

theorem cross_fraction_eq (i j : Option (Fin 2)) (m n : ℕ) (H G : PlaneRing K)
    (h : H * X j ^ n = G * X i ^ m) :
    coordinateFraction K i m H = coordinateFraction K j n G := by
  apply (((coordinate_unit K i).pow m).mul ((coordinate_unit K j).pow n)).mul_right_cancel
  calc
    _ = (coordinateFraction K i m H * polynomialMap K (X i) ^ m) *
      polynomialMap K (X j) ^ n := by ring
    _ = polynomialMap K H * polynomialMap K (X j) ^ n := by rw [coordinateFraction_clear]
    _ = polynomialMap K G * polynomialMap K (X i) ^ m := by
      simpa only [map_mul, map_pow] using congrArg (polynomialMap K) h
    _ = (coordinateFraction K j n G * polynomialMap K (X j) ^ n) *
      polynomialMap K (X i) ^ m := by rw [coordinateFraction_clear]
    _ = _ := by ring

def laurentCoordinateMap (i : Option (Fin 2)) :
    Localization.Away (X i : PlaneRing K) →+* PlaneLaurentTripleBasis.tripleRing K :=
  (TripleCoordinateLocalization.productLaurentEquiv K).toRingHom.comp (coordinateMap K i)

theorem laurent_fraction_clear (i : Option (Fin 2)) (n : ℕ) (H : PlaneRing K) :
    TripleCoordinateLocalization.productLaurentEquiv K (coordinateFraction K i n H) *
      TripleCoordinateLocalization.productLaurentEquiv K (polynomialMap K (X i)) ^ n =
        TripleCoordinateLocalization.productLaurentEquiv K (polynomialMap K H) := by
  simpa only [map_mul, map_pow] using
    congrArg (TripleCoordinateLocalization.productLaurentEquiv K) (coordinateFraction_clear K i n H)

end Cylinder.CommonTorusFractions

end
