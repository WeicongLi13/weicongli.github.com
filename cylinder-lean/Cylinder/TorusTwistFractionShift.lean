module

public import Cylinder.ChartTorusEvaluation

/-! A degree-v coordinate frame shifts the denominator exponent
of the literal torus fraction by v, including negative twists. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.TorusTwistFractionShift

open MvPolynomial Cylinder.CoordinateLaurentLocalization Cylinder.CommonTorusFractions
open Cylinder.ChartTorusEvaluation Cylinder.CoordinateChartPermutation

set_option autoImplicit false

variable (K : Type*) [Field K]

theorem frame_power_balance (i : Index) (v : ℤ) (m n : ℕ) (hd : (m : ℤ) - n = v) :
    (((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
      polynomialMap K (X i) ^ n = polynomialMap K (X i) ^ m := by
  have hu : (coordinateUnit K i) ^ v * (coordinateUnit K i) ^ n = (coordinateUnit K i) ^ m := by
    calc
      _ = (coordinateUnit K i) ^ (v + (n : ℤ)) := by rw [zpow_add, zpow_natCast]
      _ = (coordinateUnit K i) ^ (m : ℤ) := by congr 1; omega
      _ = _ := zpow_natCast _ _
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, coordinateUnit_value] using
    congrArg (fun u : (TorusRing K)ˣ => (u : TorusRing K)) hu

theorem shifted_fraction (i : Index) (v : ℤ) (m n : ℕ) (H : PlaneRing K)
    (hd : (m : ℤ) - n = v) :
    (((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
      coordinateFraction K i m H = coordinateFraction K i n H := by
  apply ((coordinate_unit K i).pow n).mul_right_cancel
  calc
    _ = coordinateFraction K i m H *
      ((((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
        polynomialMap K (X i) ^ n) := by ring
    _ = coordinateFraction K i m H * polynomialMap K (X i) ^ m := by
      rw [frame_power_balance K i v m n hd]
    _ = polynomialMap K H := coordinateFraction_clear K i m H
    _ = _ := (coordinateFraction_clear K i n H).symm

end Cylinder.TorusTwistFractionShift

end
