module

public import Cylinder.GlobalTwistPairFractionRepresentatives
public import Cylinder.TorusTwistFractionShift

/-! The canonical K-linear value of an actual pair-chart section in
the common affine torus. This uses the original homogeneous-localization
map and the literal coordinate frame. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.GlobalTwistPairSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PairTorusEvaluation

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistPairSections Cylinder.CommonTorusFractions Cylinder.ChartTorusEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem product_coordinate_unit (i j : Option (Fin 2)) :
    IsUnit (polynomialMap K (X i * X j)) := by
  rw [map_mul]
  exact (coordinate_unit K i).mul (coordinate_unit K j)

def pairCoordinateMap (i j : Option (Fin 2)) :
    Localization.Away (X i * X j : PlaneRing K) →+* TorusRing K :=
  IsLocalization.Away.lift (X i * X j) (product_coordinate_unit K i j)

theorem pairCoordinateMap_algebraMap (i j : Option (Fin 2)) (H : PlaneRing K) :
    pairCoordinateMap K i j
      (algebraMap (PlaneRing K) (Localization.Away (X i * X j : PlaneRing K)) H) =
        polynomialMap K H :=
  IsLocalization.Away.lift_eq (X i * X j) (product_coordinate_unit K i j) H

def pairRingMap (i j : Option (Fin 2)) : pairRing K i j →+* TorusRing K :=
  (pairCoordinateMap K i j).comp
    (algebraMap (pairRing K i j) (Localization.Away (X i * X j : PlaneRing K)))

theorem pairRingMap_constant (i j : Option (Fin 2)) (a : K) :
    pairRingMap K i j (constantFraction K i j a) = algebraMap K (TorusRing K) a := by
  change pairCoordinateMap K i j (constantFraction K i j a).val = _
  rw [constantFraction_val, IsScalarTower.algebraMap_apply K (PlaneRing K)
    (Localization.Away (X i * X j : PlaneRing K)) a, pairCoordinateMap_algebraMap]
  change polynomialMap K (C a) = _
  simp only [polynomialMap, RingHom.comp_apply, CurvePolarLocal.dehomogenize_C]
  exact (IsScalarTower.algebraMap_apply K (AffineRing K) (TorusRing K) a).symm

theorem pairRingMap_smul (i j : Option (Fin 2)) (a : K) (c : pairRing K i j) :
    pairRingMap K i j (a • c) = a • pairRingMap K i j c := by
  rw [smul_eq_constant_mul, map_mul, pairRingMap_constant]
  exact (Algebra.smul_def _ _).symm

def pairRingLinearMap (i j : Option (Fin 2)) : pairRing K i j →ₗ[K] TorusRing K where
  __ := (pairRingMap K i j).toAddMonoidHom
  map_smul' := pairRingMap_smul K i j

def torusValue (i j : Option (Fin 2)) (v : ℤ) :
    Γ(twist K v, pairOpen K i j) →ₗ[K] TorusRing K :=
  (LinearMap.mul K (TorusRing K)
    (((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K)).comp
      ((pairRingLinearMap K i j).comp (sectionLinearEquiv K i j v).symm.toLinearMap)

theorem pairRingMap_mk_clear (i j : Option (Fin 2)) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (2 : ℕ))) :
    pairRingMap K i j
      (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH) *
        polynomialMap K (X i * X j) ^ m = polynomialMap K H := by
  change pairCoordinateMap K i j
    (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH).val * _ = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  have he := congrArg (pairCoordinateMap K i j)
    (IsLocalization.mk'_spec (M := Submonoid.powers (X i * X j : PlaneRing K))
      (Localization.Away (X i * X j : PlaneRing K)) H ⟨(X i * X j) ^ m, m, rfl⟩)
  simpa only [map_mul, pairCoordinateMap_algebraMap, map_pow] using he

theorem torusValue_mk_clear (i j : Option (Fin 2)) (v : ℤ) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (2 : ℕ))) :
    torusValue K i j v
      (sectionLinearEquiv K i j v
        (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH)) *
        (polynomialMap K (X i) ^ (-v).toNat * polynomialMap K (X i * X j) ^ m) =
      polynomialMap K (X i ^ v.toNat * H) := by
  change ((((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
    pairRingMap K i j ((sectionLinearEquiv K i j v).symm
      (sectionLinearEquiv K i j v
        (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH)))) * _ = _
  rw [LinearEquiv.symm_apply_apply]
  calc
    _ = ((((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
        polynomialMap K (X i) ^ (-v).toNat) *
      (pairRingMap K i j
        (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH) *
          polynomialMap K (X i * X j) ^ m) := by ring
    _ = polynomialMap K (X i) ^ v.toNat * polynomialMap K H := by
      rw [TorusTwistFractionShift.frame_power_balance K i v v.toNat (-v).toNat (by omega),
        pairRingMap_mk_clear]
    _ = _ := by rw [map_mul, map_pow]

end Cylinder.PairTorusEvaluation
end
