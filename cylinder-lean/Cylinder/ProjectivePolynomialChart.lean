module

public import Cylinder.PlaneHomogenization
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! The degree-zero localization of the homogeneous polynomial ring at
the first coordinate is the actual affine polynomial ring. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectivePolynomialChart

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open Cylinder.PlaneHomogenization

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev grading := homogeneousSubmodule (Option (Fin 2)) K

abbrev ChartRing := HomogeneousLocalization.Away (grading K)
  (X none : HomogeneousPlanePolynomial (K := K))

theorem coordinate_mem : (X none : HomogeneousPlanePolynomial (K := K)) ∈ grading K 1 :=
  isHomogeneous_X K none

def toAffine : ChartRing K →+* PlanePolynomial (K := K) :=
  (IsLocalization.Away.lift
    (S := Localization.Away (X none : HomogeneousPlanePolynomial (K := K)))
    (g := dehomogenize) (X none) (by simp)).comp
    (algebraMap (ChartRing K)
      (Localization.Away (X none : HomogeneousPlanePolynomial (K := K))))

theorem toAffine_mk (n : ℕ) (a : HomogeneousPlanePolynomial (K := K))
    (ha : a ∈ grading K (n • (1 : ℕ))) :
    toAffine K (HomogeneousLocalization.Away.mk (grading K)
      (coordinate_mem K) n a ha) = dehomogenize a := by
  simp only [toAffine, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  unfold IsLocalization.Away.lift
  rw [Localization.mk_eq_mk', IsLocalization.lift_mk'_spec]
  simp

theorem toAffine_surjective : Function.Surjective (toAffine K) := by
  intro f
  have hf : homogenize f.totalDegree f ∈ grading K (f.totalDegree • (1 : ℕ)) := by
    simpa using homogenize_homogeneous f.totalDegree f le_rfl
  refine ⟨HomogeneousLocalization.Away.mk (grading K)
    (coordinate_mem K) f.totalDegree (homogenize f.totalDegree f) hf, ?_⟩
  rw [toAffine_mk, dehomogenize_homogenize]

theorem toAffine_injective [Infinite K] : Function.Injective (toAffine K) := by
  apply (injective_iff_map_eq_zero (toAffine K)).mpr
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading K)
    (coordinate_mem K) x
  have hzero : dehomogenize a = 0 := (toAffine_mk K n a ha).symm.trans hx
  have hhom : a.IsHomogeneous n := by simpa using ha
  have ha0 := dehomogenize_zero_of_homogeneous n a hhom hzero
  subst a
  apply HomogeneousLocalization.mk_eq_zero_of_num
  rfl

def chartEquiv [Infinite K] : ChartRing K ≃+* PlanePolynomial (K := K) :=
  RingEquiv.ofBijective (toAffine K) ⟨toAffine_injective K, toAffine_surjective K⟩

theorem chartEquiv_mk [Infinite K] (n : ℕ)
    (a : HomogeneousPlanePolynomial (K := K))
    (ha : a ∈ grading K (n • (1 : ℕ))) :
    chartEquiv K (HomogeneousLocalization.Away.mk (grading K)
      (coordinate_mem K) n a ha) = dehomogenize a :=
  toAffine_mk K n a ha

end Cylinder.ProjectivePolynomialChart

end
