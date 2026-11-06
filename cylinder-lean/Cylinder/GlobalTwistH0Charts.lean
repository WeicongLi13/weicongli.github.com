module

public import Cylinder.SheafLaurentZero
public import Cylinder.GlobalTwistChartLaurent
public import Cylinder.GlobalTwistKSheaf
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The actual three-chart cover and its ordered section module.
The polynomial target is finite dimensional in every integer degree. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistH0Charts

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def orderedChart (i : Fin 3) : (plane K).Opens :=
  coordinateOpen K (_root_.finSuccEquiv 2 i)

theorem orderedChart_cover : (⊤ : (plane K).Opens) ≤ iSup (orderedChart K) := by
  intro q _
  obtain ⟨i, hi⟩ := not_forall.mp
    (ProjectiveCompleteIntersectionCover.not_all_variables_mem q)
  apply Opens.mem_iSup.mpr
  refine ⟨(_root_.finSuccEquiv 2).symm i, ?_⟩
  change q ∈ coordinateOpen K (_root_.finSuccEquiv 2 ((_root_.finSuccEquiv 2).symm i))
  rw [Equiv.apply_symm_apply]
  exact hi

instance integerForms_finiteDimensional (v : ℤ) :
    FiniteDimensional K (PlaneLaurentHomogeneous.integerForms K v) := by
  by_cases hv : 0 ≤ v
  · change FiniteDimensional K
      ↥(if 0 ≤ v then homogeneousSubmodule (Option (Fin 2)) K v.toNat else
        (⊥ : Submodule K (PlaneRing K)))
    rw [ite_eq_left hv]
    exact Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Option (Fin 2)) K v.toNat)
  · change FiniteDimensional K
      ↥(if 0 ≤ v then homogeneousSubmodule (Option (Fin 2)) K v.toNat else
        (⊥ : Submodule K (PlaneRing K)))
    rw [ite_eq_right hv]
    infer_instance

variable [Infinite K]

def orderedSectionsEquiv (v : ℤ) :
    (∀ i : Fin 3, (GlobalTwistKSheaf.twistK K v).obj.obj (op (orderedChart K i))) ≃ₗ[K]
      PlaneLaurentCech.ZeroCochains (K := K) v :=
  (SheafLaurentZero.tripleEquiv K
    (fun i => (GlobalTwistKSheaf.twistK K v).obj.obj (op (orderedChart K i)))).trans
      (GlobalTwistChartLaurent.zeroSectionsEquiv K v)

end Cylinder.GlobalTwistH0Charts
end
