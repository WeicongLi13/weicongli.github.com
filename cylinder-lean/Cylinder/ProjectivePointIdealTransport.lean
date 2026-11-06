module

public import Cylinder.ProjectiveChartData
public import Cylinder.ResidualEvaluation
public import Cylinder.ResidualIntegerPieces

/-! The original projective point ideal equals the transported chart point ideal. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectivePointIdealTransport

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.ProjectiveChartData Cylinder.CurvePolarLocal Cylinder.FiniteEvaluationDuality
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation
open Cylinder.CompleteIntersectionAffinePoints Cylinder.PlaneLineCoordinates

variable {K : Type*} [Field K]

local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra
local instance : GradedAlgebra (HomForms K) := MvPolynomial.gradedAlgebra

def originalPointIdeal (D : Finset (PlanePointModel.Plane K)) : Ideal (PlaneRing K) :=
  (vanishingIdeal (PlanePointModel.representatives D)).toIdeal

theorem homogeneous_point_membership (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (H : PlaneRing K) (n : ℕ) (hH : H.IsHomogeneous n) :
    c.coordinates H ∈ (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal ↔
      H ∈ originalPointIdeal D := by
  change chartCoordinates c.a c.b c.ha c.hb H ∈
    (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal ↔ H ∈ originalPointIdeal D
  rw [homogeneous_mem_pointIdeal _ _ n (chartCoordinates_homogeneous c.a c.b c.ha c.hb H n hH),
    AffinePointEvaluation.mem_polynomialPointIdeal]
  change (∀ P : D, eval (c.affinePoint P.val) (dehomogenize (c.coordinates H)) = 0) ↔
    H ∈ (vanishingIdeal (PlanePointModel.representatives D)).toIdeal
  rw [homogeneous_mem_vanishingIdeal _ H n hH]
  constructor
  · intro h P
    have hP := h P
    change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb H)) = 0 at hP
    rw [← affineForm_eq_dehomogenize, eval_affineForm_normalized c.a c.b c.ha c.hb
      P.val.rep (hchart P) H n hH] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero n (inv_ne_zero (hchart P)))
  · intro h P
    change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb H)) = 0
    rw [← affineForm_eq_dehomogenize, eval_affineForm_normalized c.a c.b c.ha c.hb
      P.val.rep (hchart P) H n hH]
    rw [show eval P.val.rep H = 0 from h P, mul_zero]

/-- This equality holds for the complete actual ideals, rather than just
their individual homogeneous equations. -/
theorem pointIdeal_comap (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) :
    Ideal.comap c.coordinates (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal =
      originalPointIdeal D := by
  apply le_antisymm
  · intro H hH
    have ht : c.coordinates H ∈
        (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal := hH
    suffices hh : c.coordinates.symm (c.coordinates H) ∈ originalPointIdeal D by
      simpa only [AlgEquiv.symm_apply_apply] using hh
    rw [← DirectSum.sum_support_decompose (HomForms K) (c.coordinates H), map_sum]
    apply Ideal.sum_mem
    intro n hn
    let Q := DirectSum.decompose (HomForms K) (c.coordinates H) n
    have hQmem : Q.val ∈ (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal :=
      ((homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).isHomogeneous.mem_iff.mp ht) n
    have hQback := PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb
      Q.val n Q.property
    apply (homogeneous_point_membership c D hchart (c.coordinates.symm Q.val) n hQback).mp
    simpa only [AlgEquiv.apply_symm_apply] using hQmem
  · intro H hH
    change c.coordinates H ∈ (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal
    rw [← DirectSum.sum_support_decompose (Forms K) H, map_sum]
    apply Ideal.sum_mem
    intro n hn
    let Q := DirectSum.decompose (Forms K) H n
    have hQmem : Q.val ∈ originalPointIdeal D :=
      ((vanishingIdeal (PlanePointModel.representatives D)).isHomogeneous.mem_iff.mp hH) n
    exact (homogeneous_point_membership c D hchart Q.val n Q.property).mpr hQmem

def integerPlaneForms (K : Type*) [Field K] (d : ℤ) : Submodule K (PlaneRing K) :=
  if 0 ≤ d then Forms K d.toNat else ⊥

theorem integerForms_comap (c : Chart K) (d : ℤ) :
    integerPlaneForms K d = (Cylinder.ResidualIntegerPieces.integerForms K d).comap c.coordinates.toLinearMap := by
  ext H
  by_cases hd : 0 ≤ d
  · simp only [integerPlaneForms, Cylinder.ResidualIntegerPieces.integerForms, if_pos hd,
      Submodule.mem_comap]
    constructor
    · exact chartCoordinates_homogeneous c.a c.b c.ha c.hb H d.toNat
    · intro hH
      have hh := PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb
        (c.coordinates H) d.toNat hH
      change (c.coordinates.symm (c.coordinates H)).IsHomogeneous d.toNat at hh
      apply (mem_homogeneousSubmodule _ _).mpr
      simpa only [AlgEquiv.symm_apply_apply] using hh
  · simp only [integerPlaneForms, Cylinder.ResidualIntegerPieces.integerForms, if_neg hd,
      Submodule.mem_bot, Submodule.mem_comap]
    constructor
    · intro hH
      rw [hH, map_zero]
    · intro hH
      change c.coordinates H = 0 at hH
      apply c.coordinates.injective
      simpa only [map_zero] using hH

end Cylinder.ProjectivePointIdealTransport

end
