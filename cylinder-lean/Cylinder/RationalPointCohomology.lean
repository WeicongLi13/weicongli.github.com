module

public import Cylinder.RationalPointEvaluationExact
public import Cylinder.RationalPointIdealSections
public import Cylinder.RationalGlobalEvaluationCokernel
public import Cylinder.GlobalProjectiveTwistH1
public import Cylinder.ProjectiveIntegerRelations
public import Cylinder.RationalPointChartChoice
public import Cylinder.IntegerCharacterFormulas

/-! Ext-defined cohomology of the actual evaluation ideal sheaf.
The canonical scalar action and genuine long exact sequence identify
its H¹ with the original finite-point polynomial evaluation cokernel. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.SheafCohomologyScalarAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointCohomology

open CategoryTheory CategoryTheory.Limits Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.RationalPointIdealSheaf
open Cylinder.SheafCohomologyScalarAction

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] [Infinite K] {I : Type u} [Fintype I]

local instance moduleSheafZeroMorphisms (X : TopCat.{u}) :
    HasZeroMorphisms (TopCat.Sheaf (ModuleCat.{u} K) X) :=
  RationalPointIdealSheaf.moduleSheafZeroMorphisms K X

abbrev cohomologyOne (v : ℤ) (x : I → Fin 2 → K) :=
  CategoryTheory.Sheaf.H (forgetModules.obj (idealTwist K v x)) 1

def cohomologyCokernelEquiv (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    cohomologyOne K v x ≃ₗ[K]
      ((I → K) ⧸ RationalEvaluationDefect.evaluationSpace K v x) := by
  letI : Subsingleton (CategoryTheory.Sheaf.H
      (forgetModules.obj (RationalPointEvaluationExact.sequence K v x).X₂) 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H
      (forgetModules.obj (GlobalTwistKSheaf.twistK K v)) 1)
    exact GlobalProjectiveTwistH1.cohomologyOne_subsingleton K v
  exact (SheafCohomologyLinearCokernel.globalSectionsCokernelLinearEquiv
    (S := RationalPointEvaluationExact.sequence K v x)
    (RationalPointEvaluationExact.additiveSequence_shortExact K v x hx) isTerminalTop).symm.trans
      (RationalGlobalEvaluationCokernel.sectionCokernelEquiv K v x)

theorem cohomologyOne_finiteDimensional (v : ℤ) (x : I → Fin 2 → K)
    (hx : Function.Injective x) : FiniteDimensional K (cohomologyOne K v x) :=
  Module.Finite.of_injective (cohomologyCokernelEquiv K v x hx).toLinearMap
    (cohomologyCokernelEquiv K v x hx).injective

theorem cohomologyOne_finrank (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    Module.finrank K (cohomologyOne K v x) =
      Fintype.card I - RationalEvaluationDefect.hilbert K v x :=
  (cohomologyCokernelEquiv K v x hx).finrank_eq.trans
    (RationalEvaluationDefect.cokernel_finrank K v x)

theorem cohomologyOne_finrank_eq_relations (v : ℤ) (x : I → Fin 2 → K)
    (hx : Function.Injective x) :
    Module.finrank K (cohomologyOne K v x) =
      Module.finrank K (IntegerEvaluationDuality.integerCoefficientRelations x v) :=
  (cohomologyCokernelEquiv K v x hx).finrank_eq.trans
    (RationalEvaluationDefect.cokernel_finrank_eq_original_relations K v x)

theorem chart_cohomologyOne_finrank (v : ℤ) (c : ProjectiveChartData.Chart K)
    (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) :
    Module.finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) =
      Module.finrank K (ProjectiveIntegerRelations.originalRelations c D v) := by
  rw [cohomologyOne_finrank_eq_relations K v _
    (ProjectiveChartData.affinePoints_injective c D hchart)]
  exact (ProjectiveIntegerRelations.originalRelationsEquiv c D hchart v).finrank_eq.symm

theorem chart_cohomologyOne_finrank_eq_original_defect (v : ℤ)
    (c : ProjectiveChartData.Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) :
    Module.finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) =
      IntegerCharacterFormulas.integerDefect (fun P : D => P.val.rep) v := by
  rw [chart_cohomologyOne_finrank K v c D hchart]
  exact (RationalPointChartChoice.originalRelations_finrank K c D hchart v).trans
    (IntegerCharacterFormulas.integerDefect_eq_relations _ v).symm

theorem exists_common_chart_cohomology (D : Finset (PlanePointModel.Plane K)) :
    ∃ c : ProjectiveChartData.Chart K, (∀ P : D, c.line P.val.rep ≠ 0) ∧
      ∀ v : ℤ,
        Module.finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) =
          IntegerCharacterFormulas.integerDefect (fun P : D => P.val.rep) v := by
  obtain ⟨c, hc⟩ := RationalPointChartChoice.exists_common_chart K D
  exact ⟨c, hc, fun v => chart_cohomologyOne_finrank_eq_original_defect K v c D hc⟩

end Cylinder.RationalPointCohomology
end
