module

public import Cylinder.GlobalTwistKSheaf
public import Cylinder.ProjectivePointInProj

/-! Evaluation is defined on the image of the smaller localization at
the normalized affine point. This avoids evaluating the whole localization
at a homogeneous ray prime, where such evaluation would be invalid. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalFractionEvaluation

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.ProjectivePointInProj
open Cylinder.AffineIntersectionLocalRings Cylinder.AffineIntersectionPoints
open Cylinder.CurvePolarLocal

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev normalized (x : Fin 2 → K) : Option (Fin 2) → K := fun i => i.elim 1 x

abbrev PointLocalization (x : Fin 2 → K) := PointLocal (normalized K x)

theorem ray_le_pointIdeal (x : Fin 2 → K) :
    (rayPoint x).asHomogeneousIdeal.toIdeal ≤ pointIdeal (normalized K x) := by
  intro H hH
  have h := Ideal.toIdeal_homogeneousCore_le (grading K) (evaluationIdeal x) hH
  change eval x (dehomogenize H) = 0 at h
  change eval (normalized K x) H = 0
  simpa only [eval_dehomogenize, normalized] using h

def pointResidue (x : Fin 2 → K) : PointLocalization K x →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := (pointIdeal (normalized K x)).primeCompl)
    (S := PointLocalization K x) (f := polynomialEvaluation (normalized K x))
    (fun b => isUnit_iff_ne_zero.mpr (fun hb => b.property hb))

def toFull (x : Fin 2 → K) : PointLocalization K x →ₐ[K] FullLocal K (rayPoint x) :=
  IsLocalization.liftAlgHom
    (M := (pointIdeal (normalized K x)).primeCompl) (S := PointLocalization K x)
    (f := IsScalarTower.toAlgHom K (PlaneRing K) (FullLocal K (rayPoint x)))
    (fun b => IsLocalization.map_units
      (M := (rayPoint x).asHomogeneousIdeal.toIdeal.primeCompl) (FullLocal K (rayPoint x))
      ⟨b.val, fun hb => b.property (ray_le_pointIdeal K x hb)⟩)

theorem toFull_algebraMap (x : Fin 2 → K) (H : PlaneRing K) :
    toFull K x (algebraMap (PlaneRing K) (PointLocalization K x) H) =
      algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) H := by
  simp [toFull, IsLocalization.liftAlgHom_apply]

theorem toFull_injective (x : Fin 2 → K) : Function.Injective (toFull K x) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (pointIdeal (normalized K x)).primeCompl (toFull K x).toRingHom).mpr
  intro H G
  constructor
  · intro h
    exact congrArg (toFull K x) h
  · intro h
    change toFull K x (algebraMap (PlaneRing K) (PointLocalization K x) H) =
      toFull K x (algebraMap (PlaneRing K) (PointLocalization K x) G) at h
    rw [toFull_algebraMap, toFull_algebraMap] at h
    have hinj : Function.Injective
        (algebraMap (PlaneRing K) (FullLocal K (rayPoint x))) :=
      IsLocalization.injective _ (rayPoint x).asHomogeneousIdeal.toIdeal.primeCompl_le_nonZeroDivisors
    exact congrArg (algebraMap (PlaneRing K) (PointLocalization K x)) (hinj h)

def rangeEquiv (x : Fin 2 → K) : PointLocalization K x ≃ₐ[K] (toFull K x).range :=
  AlgEquiv.ofInjective (toFull K x) (toFull_injective K x)

def rangeEvaluation (x : Fin 2 → K) : (toFull K x).range →ₐ[K] K :=
  (pointResidue K x).comp (rangeEquiv K x).symm.toAlgHom

theorem homogeneous_denominator_nonzero (x : Fin 2 → K) (B : PlaneRing K)
    (n : ℕ) (hB : B.IsHomogeneous n) (hb : B ∉ (rayPoint x).asHomogeneousIdeal) :
    eval (normalized K x) B ≠ 0 := by
  intro h
  apply hb
  exact (homogeneous_mem_rayIdeal x B n hB).mpr
    (by simpa only [eval_dehomogenize, normalized] using h)

theorem fraction_mem_range (x : Fin 2 → K) (H B : PlaneRing K)
    (n : ℕ) (hB : B.IsHomogeneous n) (hb : B ∉ (rayPoint x).asHomogeneousIdeal) :
    (Localization.mk H ⟨B, hb⟩ : FullLocal K (rayPoint x)) ∈ (toFull K x).range := by
  let b : (pointIdeal (normalized K x)).primeCompl :=
    ⟨B, homogeneous_denominator_nonzero K x B n hB hb⟩
  refine ⟨IsLocalization.mk' (PointLocalization K x) H b, ?_⟩
  change toFull K x (IsLocalization.mk' (PointLocalization K x) H b) = _
  rw [Localization.mk_eq_mk'_apply]
  symm
  apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
  change algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) H =
    toFull K x (IsLocalization.mk' (PointLocalization K x) H b) *
      algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) B
  rw [← toFull_algebraMap K x H, ← toFull_algebraMap K x B, ← map_mul,
    IsLocalization.mk'_spec]

theorem rangeEvaluation_toFull (x : Fin 2 → K) (z : PointLocalization K x) :
    rangeEvaluation K x (rangeEquiv K x z) = pointResidue K x z := by
  simp only [rangeEvaluation, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]

def polynomialInRange (x : Fin 2 → K) (H : PlaneRing K) : (toFull K x).range :=
  ⟨algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) H,
    ⟨algebraMap (PlaneRing K) (PointLocalization K x) H, toFull_algebraMap K x H⟩⟩

theorem rangeEvaluation_polynomial (x : Fin 2 → K) (H : PlaneRing K) :
    rangeEvaluation K x (polynomialInRange K x H) = eval (normalized K x) H := by
  have h : polynomialInRange K x H =
      rangeEquiv K x (algebraMap (PlaneRing K) (PointLocalization K x) H) := by
    apply Subtype.ext
    exact (toFull_algebraMap K x H).symm
  rw [h, rangeEvaluation_toFull]
  simp [pointResidue, IsLocalization.liftAlgHom_apply, polynomialEvaluation]

theorem rangeEvaluation_fraction (x : Fin 2 → K) (H B : PlaneRing K)
    (n : ℕ) (hB : B.IsHomogeneous n) (hb : B ∉ (rayPoint x).asHomogeneousIdeal)
    (hm : (Localization.mk H ⟨B, hb⟩ : FullLocal K (rayPoint x)) ∈ (toFull K x).range) :
    rangeEvaluation K x ⟨Localization.mk H ⟨B, hb⟩, hm⟩ =
      eval (normalized K x) H / eval (normalized K x) B := by
  apply (eq_div_iff (homogeneous_denominator_nonzero K x B n hB hb)).mpr
  rw [← rangeEvaluation_polynomial K x B, ← map_mul]
  have h : (⟨Localization.mk H ⟨B, hb⟩, hm⟩ : (toFull K x).range) *
      polynomialInRange K x B = polynomialInRange K x H := by
    apply Subtype.ext
    change Localization.mk H ⟨B, hb⟩ *
      algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) B =
        algebraMap (PlaneRing K) (FullLocal K (rayPoint x)) H
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec _ H ⟨B, hb⟩
  rw [h, rangeEvaluation_polynomial]

end Cylinder.RationalFractionEvaluation
end
