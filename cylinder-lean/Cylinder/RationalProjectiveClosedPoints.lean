module

public import Cylinder.RationalFractionEvaluation

/-! Normalized rational points are closed in the actual projective
scheme, including against all non-rational homogeneous prime points. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalProjectiveClosedPoints

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.ProjectivePointInProj Cylinder.RationalFractionEvaluation Cylinder.CurvePolarLocal
open Cylinder.GlobalTwistLocalFractions

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem coordinate_relation (x : Fin 2 → K) (j : Fin 2) :
    (X (some j) - C (x j) * X none : PlaneRing K) ∈ (rayPoint x).asHomogeneousIdeal := by
  apply (homogeneous_mem_rayIdeal x _ 1
    ((isHomogeneous_X K (some j)).sub (by
      simpa only [zero_add] using (isHomogeneous_C (Option (Fin 2)) (x j)).mul
        (isHomogeneous_X K none)))).mpr
  simp

theorem coordinate_avoids_above_ray (x : Fin 2 → K) (q : plane K)
    (hle : (rayPoint x).asHomogeneousIdeal ≤ q.asHomogeneousIdeal) :
    (X none : PlaneRing K) ∉ q.asHomogeneousIdeal := by
  intro hnone
  have hvars (j : Option (Fin 2)) : (X j : PlaneRing K) ∈ q.asHomogeneousIdeal := by
    cases j with
    | none => exact hnone
    | some j =>
      change X (some j) ∈ q.asHomogeneousIdeal.toIdeal
      have hrel := hle (coordinate_relation K x j)
      have hmul := q.asHomogeneousIdeal.toIdeal.mul_mem_left (C (x j)) hnone
      simpa only [sub_add_cancel] using q.asHomogeneousIdeal.toIdeal.add_mem hrel hmul
  exact Cylinder.ProjectiveCompleteIntersectionCover.not_all_variables_mem q hvars

theorem rayPoint_maximal (x : Fin 2 → K) (q : plane K)
    (hle : rayPoint x ≤ q) : q = rayPoint x := by
  have hle' : (rayPoint x).asHomogeneousIdeal ≤ q.asHomogeneousIdeal := hle
  have hnone := coordinate_avoids_above_ray K x q hle'
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n H hH
  change H.IsHomogeneous n at hH
  constructor
  · intro hq
    apply (homogeneous_mem_rayIdeal x H n hH).mpr
    by_contra ha
    let a := eval x (dehomogenize H)
    have hd : H - C a * X none ^ n ∈ (rayPoint x).asHomogeneousIdeal := by
      apply (homogeneous_mem_rayIdeal x _ n
        (hH.sub (by simpa only [zero_add] using
          (isHomogeneous_C (Option (Fin 2)) a).mul (isHomogeneous_X_pow none n)))).mpr
      simp [a]
    have hp : C a * X none ^ n ∈ q.asHomogeneousIdeal := by
      change C a * X none ^ n ∈ q.asHomogeneousIdeal.toIdeal
      simpa only [sub_sub_cancel] using q.asHomogeneousIdeal.toIdeal.sub_mem hq (hle' hd)
    rcases q.isPrime.mem_or_mem hp with hc | hx
    · exact Ideal.notMem_of_isUnit q.asHomogeneousIdeal.toIdeal
        ((isUnit_iff_ne_zero.mpr ha).map (C : K →+* PlaneRing K)) hc
    · exact hnone (q.isPrime.mem_of_pow_mem n hx)
  · exact fun h => hle' h

theorem isClosed_rayPoint (x : Fin 2 → K) :
    IsClosed ({rayPoint x} : Set (plane K)) := by
  apply isClosed_of_closure_subset
  intro q hq
  exact Set.mem_singleton_iff.mpr (rayPoint_maximal K x q
    ((ProjectiveSpectrum.le_iff_mem_closure (grading K) (rayPoint x) q).mpr hq))

theorem isClosed_finite_points {I : Type*} [Finite I] (x : I → Fin 2 → K) :
    IsClosed (Set.range (fun i => rayPoint (x i)) : Set (plane K)) := by
  simpa only [Set.iUnion_singleton_eq_range] using
    isClosed_iUnion_of_finite (fun i => isClosed_rayPoint K (x i))

end Cylinder.RationalProjectiveClosedPoints
end
