module

public import Cylinder.CoordinateTwistLaurentPiece
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! The actual degree-v homogeneous fractions are a module for the
actual degree-zero homogeneous coordinate localization. The action is
the original multiplication in the full localization, rather than an
action transported across a vector-space equivalence. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CoordinateTwistChartModule

open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistFractions MvPolynomial

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [CommRing K]

abbrev grading := homogeneousSubmodule (Option (Fin 2)) K

abbrev chartRing := HomogeneousLocalization.Away (grading K) (X none : PlaneRing K)

theorem coordinate_mem : (X none : PlaneRing K) ∈ grading K 1 :=
  isHomogeneous_X K none

theorem fraction_mul (m n : ℕ) (p q : PlaneRing K) :
    fractionLinear K m p * fractionLinear K n q = fractionLinear K (m + n) (p * q) := by
  change IsLocalization.mk' (CoordinateLocalization K) p _ *
    IsLocalization.mk' (CoordinateLocalization K) q _ = _
  rw [← IsLocalization.mk'_mul]
  congr 1
  apply Subtype.ext
  simp only [Submonoid.coe_mul, pow_add]

theorem homogeneous_fraction_mul_mem (v : ℤ) (k : ℕ) (q : PlaneRing K)
    (hq : q.IsHomogeneous k) {z : CoordinateLocalization K} (hz : z ∈ twistPiece K v) :
    fractionLinear K k q * z ∈ twistPiece K v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, n, p, hd, hp, rfl⟩ := hz
      rw [fraction_mul]
      exact Submodule.subset_span ⟨k + m, k + n, q * p, by omega, hq.mul hp, rfl⟩
  | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ a ih

theorem chart_smul_mem (v : ℤ) (c : chartRing K) {z : CoordinateLocalization K}
    (hz : z ∈ twistPiece K v) : c • z ∈ twistPiece K v := by
  obtain ⟨k, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading K) (coordinate_mem K) c
  have hq' : q.IsHomogeneous k := by simpa using hq
  rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  exact homogeneous_fraction_mul_mem K v k q hq' hz

/-- The local twist module with its genuine coordinate-ring action. -/
def twistModule (v : ℤ) : Submodule (chartRing K) (CoordinateLocalization K) where
  carrier := twistPiece K v
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  smul_mem' := fun c _ hz => chart_smul_mem K v c hz

theorem mem_twistModule_iff (v : ℤ) (z : CoordinateLocalization K) :
    z ∈ twistModule K v ↔ z ∈ twistPiece K v := Iff.rfl

theorem twistModule_smul_coe (v : ℤ) (c : chartRing K) (z : twistModule K v) :
    ((c • z : twistModule K v) : CoordinateLocalization K) =
      algebraMap (chartRing K) (CoordinateLocalization K) c * z := rfl

end Cylinder.CoordinateTwistChartModule

end
