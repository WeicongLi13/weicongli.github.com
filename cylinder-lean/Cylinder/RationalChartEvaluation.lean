module

public import Cylinder.RationalTwistEvaluation
public import Cylinder.GlobalTwistCoordinateSections
public import Cylinder.AffinePointEvaluation

/-! On the standard affine chart, the actual twisting-sheaf evaluation
is the original polynomial evaluation. Interpolation supplies all finite
tuples of values at distinct rational points. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalChartEvaluation

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.ProjectivePointInProj Cylinder.RationalTwistEvaluation
open Cylinder.GlobalTwistCoordinateSections Cylinder.RationalFractionEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

theorem coordinateSection_evaluation (v : ℤ) (x : Fin 2 → K) (c : coordinateRing K none) :
    evaluation K v x (coordinateOpen K none) (rayPoint_mem_standardOpen x)
      (coordinateSection K none v c) = eval x (Cylinder.ProjectivePolynomialChart.chartEquiv K c) := by
  obtain ⟨m, H, hH, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading K)
    (coordinate_mem K) c
  let U := coordinateOpen K none
  let q : U := ⟨rayPoint x, rayPoint_mem_standardOpen x⟩
  let n := (-v).toNat + m
  let B : PlaneRing K := X none ^ n
  have hB : B.IsHomogeneous n := isHomogeneous_X_pow none n
  have hb : B ∉ (rayPoint x).asHomogeneousIdeal :=
    coordinate_power_avoids K none U le_rfl q n
  have hs : (coordinateSection K none v
      (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) m H hH)).val q =
      Localization.mk (X none ^ v.toNat * H) ⟨B, hb⟩ := by
    change (frame K none v U le_rfl).val q *
      ((Proj.awayToSection (grading K) (X none)
        (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) m H hH)).val q).val = _
    rw [frame_apply, GlobalTwistStandardFractions.away_mk_section_value,
      Localization.mk_mul]
    apply congrArg (Localization.mk (X none ^ v.toNat * H))
    apply Subtype.ext
    exact (pow_add (X none) (-v).toNat m).symm
  rw [evaluation_fraction K v x U (rayPoint_mem_standardOpen x) _
    (X none ^ v.toNat * H) B n hB hb hs,
    Cylinder.ProjectivePolynomialChart.chartEquiv_mk, Cylinder.CurvePolarLocal.eval_dehomogenize]
  simp only [B, normalized, map_mul, map_pow, eval_X, Option.elim_none, one_pow, one_mul, div_one]

theorem exists_section_evaluation {I : Type*} [Fintype I]
    (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) (w : I → K) :
    ∃ s : sectionsSubmodule K v (coordinateOpen K none), ∀ i,
      evaluation K v (x i) (coordinateOpen K none) (rayPoint_mem_standardOpen (x i)) s = w i := by
  obtain ⟨P, hP⟩ := Cylinder.AffinePointEvaluation.polynomialEvaluation_surjective x hx w
  refine ⟨coordinateSection K none v ((Cylinder.ProjectivePolynomialChart.chartEquiv K).symm P), ?_⟩
  intro i
  rw [coordinateSection_evaluation, RingEquiv.apply_symm_apply]
  exact congrFun hP i

end Cylinder.RationalChartEvaluation
end
