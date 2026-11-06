module

public import Cylinder.CommonTorusFractions
public import Cylinder.HomogeneousTorusRescaling
public import Cylinder.CoordinateChartLaurent

/-! The actual map from every degree-zero chart ring to the common
torus is evaluation in the literal normalized chart coordinates. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.CoordinateChartPermutation

namespace Cylinder.ChartTorusEvaluation

open MvPolynomial Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateChartPermutation Cylinder.CoordinateChartLaurent
open Cylinder.CommonTorusFractions Cylinder.CurvePolarLocal

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def coordinateUnit (i : Index) : (TorusRing K)ˣ := (coordinate_unit K i).unit

theorem coordinateUnit_value (i : Index) :
    (coordinateUnit K i : TorusRing K) = polynomialMap K (X i) := (coordinate_unit K i).unit_spec

def normalizedValues (i : Index) (j : Fin 2) : TorusRing K :=
  (((coordinateUnit K i)⁻¹ : (TorusRing K)ˣ) : TorusRing K) *
    polynomialMap K (X (Equiv.swap i none (some j)))

def chartPolynomialMap (i : Index) : AffineRing K →+* TorusRing K :=
  MvPolynomial.eval₂Hom (algebraMap K (TorusRing K)) (normalizedValues K i)

theorem polynomialMap_eval₂ (H : PlaneRing K) :
    polynomialMap K H = eval₂ (algebraMap K (TorusRing K))
      (fun i => polynomialMap K (X i)) H := by
  induction H using MvPolynomial.induction_on with
  | C a =>
    simp only [polynomialMap, RingHom.comp_apply, dehomogenize_C, eval₂_C]
    exact (IsScalarTower.algebraMap_apply K (AffineRing K) (TorusRing K) a).symm
  | add H G hH hG => simp only [map_add, eval₂_add, hH, hG]
  | mul_X H i hH => simp only [map_mul, hH, eval₂_mul, eval₂_X]

theorem normalized_homogeneous (i : Index) (m : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) :
    chartPolynomialMap K i (dehomogenize (MvPolynomial.rename (Equiv.swap i none) H)) =
      (((coordinateUnit K i)⁻¹ : (TorusRing K)ˣ) : TorusRing K) ^ m * polynomialMap K H := by
  have h := HomogeneousTorusRescaling.normalized_chart_eval
    (algebraMap K (TorusRing K)) H m hH i (fun j => polynomialMap K (X j))
    (coordinateUnit K i) (coordinateUnit_value K i)
  change eval₂ (algebraMap K (TorusRing K))
    (fun j => (((coordinateUnit K i)⁻¹ : (TorusRing K)ˣ) : TorusRing K) *
      polynomialMap K (X (Equiv.swap i none (some j))))
    (dehomogenize (MvPolynomial.rename (Equiv.swap i none) H)) = _
  rw [← polynomialMap_eval₂] at h
  exact h

theorem fraction_eq_normalized (i : Index) (m : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) :
    coordinateFraction K i m H =
      chartPolynomialMap K i (dehomogenize (MvPolynomial.rename (Equiv.swap i none) H)) := by
  apply ((coordinate_unit K i).pow m).mul_right_cancel
  rw [coordinateFraction_clear, normalized_homogeneous K i m H hH]
  have hc : (((coordinateUnit K i)⁻¹ : (TorusRing K)ˣ) : TorusRing K) ^ m *
      polynomialMap K (X i) ^ m = 1 := by
    rw [← coordinateUnit_value, ← mul_pow, Units.inv_mul, one_pow]
  symm
  calc
    _ = ((((coordinateUnit K i)⁻¹ : (TorusRing K)ˣ) : TorusRing K) ^ m *
      polynomialMap K (X i) ^ m) * polynomialMap K H := by ring
    _ = _ := by rw [hc, one_mul]

def coordinateRingMap (i : Index) : coordinateRing K i →+* TorusRing K :=
  (coordinateMap K i).comp
    (algebraMap (coordinateRing K i) (Localization.Away (X i : PlaneRing K)))

variable [Infinite K]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateRingMap_eq_normalized (i : Index) (c : coordinateRing K i) :
    coordinateRingMap K i c = chartPolynomialMap K i (affineEquiv K i c) := by
  obtain ⟨m, H, hH, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading K)
    (isHomogeneous_X K i) c
  rw [affineEquiv_mk]
  change coordinateMap K i
    (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change coordinateFraction K i m H = _
  exact fraction_eq_normalized K i m H (by simpa using hH)

end Cylinder.ChartTorusEvaluation

end
