module

public import Cylinder.CommonTorusFractions
public import Cylinder.PlaneHomogenization

/-! The common affine torus loses no information on a fixed
homogeneous degree. Equal-degree literal coordinate fractions are
equal there exactly when their original numerators cross-multiply. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.HomogeneousTorusInjectivity

open MvPolynomial Cylinder.CoordinateLaurentLocalization
open Cylinder.CommonTorusFractions Cylinder.CurvePolarLocal

set_option autoImplicit false

variable (K : Type*) [Field K]

theorem affine_injective :
    Function.Injective (algebraMap (AffineRing K) (TorusRing K)) := by
  apply IsLocalization.injective (R := AffineRing K) (S := TorusRing K)
    (M := Submonoid.powers ((X 0 : AffineRing K) * X 1))
  rintro p ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)))

variable [Infinite K]

theorem homogeneous_injective (m : ℕ) (H G : PlaneRing K)
    (hH : H.IsHomogeneous m) (hG : G.IsHomogeneous m)
    (heq : polynomialMap K H = polynomialMap K G) : H = G := by
  apply PlaneHomogenization.dehomogenize_injective_on_homogeneous m H G hH hG
  exact affine_injective K heq

theorem homogeneous_zero (m : ℕ) (H : PlaneRing K) (hH : H.IsHomogeneous m)
    (heq : polynomialMap K H = 0) : H = 0 :=
  homogeneous_injective K m H 0 hH (MvPolynomial.isHomogeneous_zero _ _ m)
    (heq.trans (map_zero _).symm)

theorem coordinateFraction_cross_iff (i j : Option (Fin 2)) (m n a b : ℕ)
    (H G : PlaneRing K) (hH : H.IsHomogeneous a) (hG : G.IsHomogeneous b)
    (hd : a + n = b + m) :
    coordinateFraction K i m H = coordinateFraction K j n G ↔
      H * X j ^ n = G * X i ^ m := by
  constructor
  · intro heq
    apply homogeneous_injective K (a + n) _ _
      (hH.mul (isHomogeneous_X_pow j n))
      (by rw [hd]; exact hG.mul (isHomogeneous_X_pow i m))
    simp only [map_mul, map_pow]
    calc
      _ = (coordinateFraction K i m H * polynomialMap K (X i) ^ m) *
        polynomialMap K (X j) ^ n := by rw [coordinateFraction_clear]
      _ = (coordinateFraction K j n G * polynomialMap K (X j) ^ n) *
        polynomialMap K (X i) ^ m := by rw [heq]; ring
      _ = _ := by rw [coordinateFraction_clear]
  · exact cross_fraction_eq K i j m n H G

end Cylinder.HomogeneousTorusInjectivity

end
