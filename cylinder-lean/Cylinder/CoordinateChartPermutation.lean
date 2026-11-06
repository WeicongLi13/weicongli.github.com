module

public import Cylinder.CoordinateTwistChartModule
public import Mathlib.Algebra.MvPolynomial.Rename

/-! Variable permutations induce actual maps of the homogeneous
coordinate localizations. The maps preserve the literal numerator
and denominator of each homogeneous fraction. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CoordinateChartPermutation

open MvPolynomial Cylinder.CoordinateLaurentLocalization
open Cylinder.CoordinateTwistChartModule

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Index := Option (Fin 2)

variable (K : Type*) [CommRing K]

abbrev coordinateRing (i : Index) :=
  HomogeneousLocalization.Away (grading K) (X i : PlaneRing K)

scoped instance coordinateKModule (i : Index) : Module K (coordinateRing K i) :=
  Function.Injective.module K
    (algebraMap (coordinateRing K i) (Localization.Away (X i : PlaneRing K))).toAddMonoidHom
    (HomogeneousLocalization.val_injective (Submonoid.powers (X i : PlaneRing K)))
    (fun a z => HomogeneousLocalization.val_smul (Submonoid.powers (X i : PlaneRing K)) a z)

open scoped Cylinder.CoordinateChartPermutation

def gradedRename (e : Index ≃ Index) : grading K →+*ᵍ grading K where
  __ := (MvPolynomial.renameEquiv K e).toRingHom
  map_mem hp := hp.rename_isHomogeneous

theorem gradedRename_inverse (e : Index ≃ Index) :
    (gradedRename K e.symm).comp (gradedRename K e) = .id (grading K) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.renameEquiv K e).left_inv p

theorem renamePowers (e : Index ≃ Index) (i j : Index) (h : e i = j) :
    Submonoid.powers (X i : PlaneRing K) ≤
      (Submonoid.powers (X j : PlaneRing K)).comap (gradedRename K e) := by
  rintro p ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  change X j ^ n = MvPolynomial.rename e (X i ^ n)
  rw [map_pow, MvPolynomial.rename_X, h]

def renameAway (e : Index ≃ Index) (i j : Index) (h : e i = j) :
    coordinateRing K i →+* coordinateRing K j :=
  HomogeneousLocalization.map (gradedRename K e) (renamePowers K e i j h)

theorem renameAway_inverse (e : Index ≃ Index) (i j : Index) (h : e i = j)
    (z : coordinateRing K i) :
    renameAway K e.symm j i (by rw [← h, Equiv.symm_apply_apply])
      (renameAway K e i j h z) = z := by
  change HomogeneousLocalization.map (gradedRename K e.symm) _
    (HomogeneousLocalization.map (gradedRename K e) _ z) = z
  rw [HomogeneousLocalization.map_map]
  simp only [gradedRename_inverse, HomogeneousLocalization.map_id, RingHom.id_apply]

def coordinateEquiv (e : Index ≃ Index) (i j : Index) (h : e i = j) :
    coordinateRing K i ≃+* coordinateRing K j where
  __ := renameAway K e i j h
  invFun := renameAway K e.symm j i (by rw [← h, Equiv.symm_apply_apply])
  left_inv := renameAway_inverse K e i j h
  right_inv z := by
    have h' : e.symm j = i := by rw [← h, Equiv.symm_apply_apply]
    exact renameAway_inverse K e.symm j i h' z

theorem renameAway_mk (e : Index ≃ Index) (i j : Index) (h : e i = j)
    (n : ℕ) (H : PlaneRing K) (hH : H ∈ grading K (n • (1 : ℕ))) :
    renameAway K e i j h
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) n H hH) =
    HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K j) n
      (MvPolynomial.rename e H) hH.rename_isHomogeneous := by
  subst j
  simp only [renameAway, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk]
  congr 1
  apply HomogeneousLocalization.NumDenSameDeg.ext
  all_goals simp [gradedRename, map_pow, MvPolynomial.rename_X]

def toFirstChart (i : Index) : coordinateRing K i ≃+* chartRing K :=
  coordinateEquiv K (Equiv.swap i none) i none (Equiv.swap_apply_left i none)

theorem toFirstChart_mk (i : Index) (n : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (n • (1 : ℕ))) :
    toFirstChart K i
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) n H hH) =
    HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n
      (MvPolynomial.rename (Equiv.swap i none) H) hH.rename_isHomogeneous :=
  renameAway_mk K (Equiv.swap i none) i none (Equiv.swap_apply_left i none) n H hH

theorem renameAway_smul (e : Index ≃ Index) (i j : Index) (h : e i = j)
    (a : K) (z : coordinateRing K i) :
    renameAway K e i j h (a • z) = a • renameAway K e i j h z := by
  unfold renameAway
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [← HomogeneousLocalization.mk_smul, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.map_mk, ← HomogeneousLocalization.mk_smul]
  congr 1
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · change MvPolynomial.rename e (a • c.num.val) = a • MvPolynomial.rename e c.num.val
    exact (MvPolynomial.rename e).toLinearMap.map_smul a c.num.val
  · rfl

def coordinateLinearEquiv (e : Index ≃ Index) (i j : Index) (h : e i = j) :
    coordinateRing K i ≃ₗ[K] coordinateRing K j where
  __ := (coordinateEquiv K e i j h).toAddEquiv
  map_smul' a z := by
    change renameAway K e i j h (a • z) = a • renameAway K e i j h z
    exact renameAway_smul K e i j h a z

def toFirstChartLinear (i : Index) : coordinateRing K i ≃ₗ[K] chartRing K :=
  coordinateLinearEquiv K (Equiv.swap i none) i none (Equiv.swap_apply_left i none)

theorem toFirstChartLinear_apply (i : Index) (z : coordinateRing K i) :
    toFirstChartLinear K i z = toFirstChart K i z := rfl

end Cylinder.CoordinateChartPermutation

end
