module

public import Cylinder.CoordinateChartPermutation
public import Cylinder.PlaneLaurentPermutation
public import Cylinder.CoordinateTwistOverlapLinear

/-! All three actual coordinate rings have compatible homogeneous
Laurent chart models. A fraction is first renamed literally, then
dehomogenized; the homogeneous exponent is carried along unchanged. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.CoordinateChartPermutation
open scoped Cylinder.CoordinateTwistOverlapLinear

namespace Cylinder.CoordinateChartLaurent

open MvPolynomial Cylinder.CoordinateLaurentLocalization
open Cylinder.CoordinateTwistChartModule Cylinder.CoordinateChartPermutation
open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentChartBasis

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateNumber (i : Index) : Fin 3 := (_root_.finSuccEquiv 2).symm i

def chartPermutation (i : Index) : Fin 3 ≃ Fin 3 := Equiv.swap 0 (coordinateNumber i)

theorem chartPermutation_first (i : Index) : chartPermutation i 0 = coordinateNumber i :=
  Equiv.swap_apply_left _ _

variable (K : Type*) [Field K] [Infinite K]

def firstAffineLinearEquiv : chartRing K ≃ₗ[K] AffineRing K where
  __ := (Cylinder.ProjectivePolynomialChart.chartEquiv K).toAddEquiv
  map_smul' a z := by
    change Cylinder.ProjectivePolynomialChart.chartEquiv K (a • z) =
      a • Cylinder.ProjectivePolynomialChart.chartEquiv K z
    have hs : a • z = CoordinateTwistOverlapLinear.coefficientMap K a * z :=
      (CoordinateTwistOverlapLinear.coefficientAlgebra K).smul_def' a z
    rw [hs, map_mul]
    change Cylinder.ProjectivePolynomialChart.chartEquiv K
      ((Cylinder.ProjectivePolynomialChart.chartEquiv K).symm (C a)) *
        Cylinder.ProjectivePolynomialChart.chartEquiv K z = _
    rw [RingEquiv.apply_symm_apply]
    exact (Algebra.smul_def a _).symm

def affineEquiv (i : Index) : coordinateRing K i ≃ₗ[K] AffineRing K :=
  (toFirstChartLinear K i).trans (firstAffineLinearEquiv K)

set_option backward.isDefEq.respectTransparency false in
theorem affineEquiv_mk (i : Index) (n : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (n • (1 : ℕ))) :
    affineEquiv K i
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) n H hH) =
      Cylinder.CurvePolarLocal.dehomogenize (MvPolynomial.rename (Equiv.swap i none) H) := by
  change Cylinder.ProjectivePolynomialChart.chartEquiv K
    (toFirstChart K i (HomogeneousLocalization.Away.mk (grading K)
      (isHomogeneous_X K i) n H hH)) = _
  rw [toFirstChart_mk]
  exact Cylinder.ProjectivePolynomialChart.chartEquiv_mk K n _ _

def chartPiecePermutation (v : ℤ) (i : Index) :
    piece (K := K) v {0} ≃ₗ[K] piece (K := K) v {coordinateNumber i} :=
  (PlaneLaurentPermutation.pieceEquiv (chartPermutation i) v {0}).trans
    (LinearEquiv.ofEq _ _ (by simp [chartPermutation]))

def chartLaurentEquiv (v : ℤ) (i : Index) :
    coordinateRing K i ≃ₗ[K] piece (K := K) v {coordinateNumber i} :=
  (affineEquiv K i).trans ((chartPolynomialEquiv v).symm.trans (chartPiecePermutation K v i))

theorem chartLaurentEquiv_mk (v : ℤ) (i : Index) (n : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (n • (1 : ℕ))) :
    chartLaurentEquiv K v i
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) n H hH) =
      chartPiecePermutation K v i ((chartPolynomialEquiv v).symm
        (Cylinder.CurvePolarLocal.dehomogenize (MvPolynomial.rename (Equiv.swap i none) H))) := by
  change chartPiecePermutation K v i ((chartPolynomialEquiv v).symm
      (affineEquiv K i (HomogeneousLocalization.Away.mk (grading K)
        (isHomogeneous_X K i) n H hH))) = _
  rw [affineEquiv_mk]

end Cylinder.CoordinateChartLaurent

end
