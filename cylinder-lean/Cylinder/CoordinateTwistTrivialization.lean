module

public import Cylinder.CoordinateTwistAffineSheaf
public import Cylinder.ProjectivePolynomialChart

/-! A genuine trivialization of the homogeneous-fraction module as a
module over the actual affine coordinate ring. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CoordinateTwistTrivialization

open MvPolynomial Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistFractions
open Cylinder.CoordinateTwistLaurentPiece Cylinder.CoordinateTwistChartModule
open Cylinder.CurvePolarLocal

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

def chartEvaluation : CoordinateLocalization K →ₐ[K] AffineRing K :=
  (evaluateOneAlgHom K).comp (localizationAlgEquiv K).toAlgHom

omit [Infinite K] in
theorem polynomial_chart_evaluation (p : PlaneRing K) :
    Polynomial.eval 1 (MvPolynomial.optionEquivLeft K (Fin 2) p) = dehomogenize p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i <;> simp [hp]

omit [Infinite K] in
theorem chartEvaluation_fraction (n : ℕ) (p : PlaneRing K) :
    chartEvaluation K (fractionLinear K n p) = dehomogenize p := by
  change LaurentPolynomial.eval₂ (RingHom.id (AffineRing K)) 1
    (localizationEquiv K (IsLocalization.mk' (CoordinateLocalization K) p
      (⟨X none ^ n, n, rfl⟩ : Submonoid.powers (X none : PlaneRing K)))) = _
  rw [localizationEquiv_fraction]
  rw [map_mul, LaurentPolynomial.eval₂_T]
  simp only [one_zpow, Units.val_one, mul_one, LaurentPolynomial.eval₂_toLaurent]
  exact polynomial_chart_evaluation K p

theorem chartEvaluation_chart_scalar (c : chartRing K) :
    chartEvaluation K (algebraMap (chartRing K) (CoordinateLocalization K) c) =
      Cylinder.ProjectivePolynomialChart.chartEquiv K c := by
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading K) (coordinate_mem K) c
  rw [Cylinder.ProjectivePolynomialChart.chartEquiv_mk]
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  exact chartEvaluation_fraction K n p

instance affineAlgebra : Algebra (chartRing K) (AffineRing K) :=
  (Cylinder.ProjectivePolynomialChart.chartEquiv K).toRingHom.toAlgebra

theorem affineAlgebra_map (c : chartRing K) :
    algebraMap (chartRing K) (AffineRing K) c =
      Cylinder.ProjectivePolynomialChart.chartEquiv K c := rfl

def twistEvaluation (v : ℤ) : twistModule K v →ₗ[chartRing K] AffineRing K where
  toFun z := chartEvaluation K z
  map_add' z w := map_add _ _ _
  map_smul' c z := by
    change chartEvaluation K
      (algebraMap (chartRing K) (CoordinateLocalization K) c * z) = _
    rw [map_mul, chartEvaluation_chart_scalar]
    rfl

omit [Infinite K] in
theorem evaluateOne_weighted (v : ℤ) (z : weightedLaurentPiece K v) :
    evaluateOneAlgHom K z = (affineWeightedEquiv K v).symm z := by
  obtain ⟨p, rfl⟩ := (affineWeightedEquiv K v).surjective z
  rw [LinearEquiv.symm_apply_apply]
  change evaluateOneAlgHom K (affineLift K v p) = p
  exact evaluateOne_affineLift K v p

def carrierEquiv (v : ℤ) : twistModule K v ≃ twistPiece K v := Equiv.refl _

theorem twistEvaluation_bijective (v : ℤ) : Function.Bijective (twistEvaluation K v) := by
  let e : twistModule K v ≃ AffineRing K :=
    (carrierEquiv K v).trans
      ((twistLaurentEquiv K v).toEquiv.trans (affineWeightedEquiv K v).symm.toEquiv)
  have he : ∀ z, twistEvaluation K v z = e z := by
    intro z
    exact evaluateOne_weighted K v (twistLaurentEquiv K v (carrierEquiv K v z))
  convert e.bijective using 1
  exact funext he

def twistAffineEquiv (v : ℤ) : twistModule K v ≃ₗ[chartRing K] AffineRing K :=
  LinearEquiv.ofBijective (twistEvaluation K v) (twistEvaluation_bijective K v)

theorem twistAffineEquiv_apply (v : ℤ) (z : twistModule K v) :
    twistAffineEquiv K v z = chartEvaluation K z := rfl

end Cylinder.CoordinateTwistTrivialization

end
