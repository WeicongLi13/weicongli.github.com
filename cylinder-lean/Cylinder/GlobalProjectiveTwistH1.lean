module

public import Cylinder.GlobalTwistAffineSectionsLift
public import Cylinder.SheafCechOneIsomorphism
public import Cylinder.GlobalTwistCoordinateCech

/-! Global H¹ descent for the actual homogeneous-fraction twist.
The coordinate Čech comparison is separated from the genuine Ext step:
the latter uses the actual global injective-cokernel sequence and the
proved affine section lifts on its three coordinate opens. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

universe u

namespace Cylinder.GlobalProjectiveTwistH1

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.GlobalTwistChartFrame Cylinder.SheafCohomologyScalarAction
open Cylinder.SheafCechOneDescent Cylinder.SheafInjectiveCokernel

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] [Infinite K]

omit [Infinite K] in
theorem coordinate_cover : (⊤ : (plane K).Opens) ≤ iSup (coordinateOpen K) := by
  intro q _
  obtain ⟨i, hi⟩ := not_forall.mp (ProjectiveCompleteIntersectionCover.not_all_variables_mem q)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem sections_surjective_of_coordinate_cech (v : ℤ)
    (hcech : CechOneExact (forgetModules.obj (twistK K v)) (coordinateOpen K))
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (plane K).toTopCat)
      AddCommGrpCat.{u})} (hS : S.ShortExact)
    (e : S.X₁ ≅ forgetModules.obj (twistK K v)) :
    Function.Surjective (S.g.hom.app (op (⊤ : (plane K).Opens))) := by
  refine sections_surjective_of_cech_one_exact hS (coordinateOpen K) (coordinate_cover K)
    (SheafCechOneIsomorphism.cech_one_exact_of_iso e _ hcech) ?_
  intro t i
  exact GlobalTwistAffineSectionsLift.lift_section K v hS e i (sectionsRestrict S.X₃ le_top t)

theorem cohomologyOne_subsingleton_of_coordinate_cech (v : ℤ)
    (hcech : CechOneExact (forgetModules.obj (twistK K v)) (coordinateOpen K)) :
    Subsingleton (CategoryTheory.Sheaf.H (forgetModules.obj (twistK K v)) 1) := by
  let F := forgetModules.obj (twistK K v)
  have hS := injectiveSequence_shortExact F
  let : Subsingleton (CategoryTheory.Sheaf.H (injectiveSequence F).X₂ 1) :=
    injective_cohomologyOne_subsingleton (Injective.under F)
  have hsurj := sections_surjective_of_coordinate_cech K v hcech hS (Iso.refl _)
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  obtain ⟨s, hs⟩ := SheafCohomologyCokernel.sectionConnecting_surjective hS isTerminalTop x
  obtain ⟨a, ha⟩ := hsurj s
  rw [← hs, ← ha]
  exact SheafCohomologyCokernel.sectionConnecting_map_zero hS isTerminalTop a

theorem cohomologyOne_subsingleton (v : ℤ) :
    Subsingleton (CategoryTheory.Sheaf.H (forgetModules.obj (twistK K v)) 1) :=
  cohomologyOne_subsingleton_of_coordinate_cech K v
    (GlobalTwistCoordinateCech.coordinate_cech_one_exact K v)

theorem cohomologyOne_eq_zero (v : ℤ)
    (x : CategoryTheory.Sheaf.H (forgetModules.obj (twistK K v)) 1) : x = 0 :=
  (cohomologyOne_subsingleton K v).elim x 0

end Cylinder.GlobalProjectiveTwistH1

end
