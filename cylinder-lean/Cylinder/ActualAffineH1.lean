module

public import Cylinder.ActualAffineSectionsLift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.RingTheory.Localization.FractionRing

/-! Genuine Ext-defined H¹ vanishing for the structure sheaf of an affine domain.
Enough injectives and the Ext-smallness structure come from the actual
Grothendieck abelian sheaf category.  The cokernel section lift follows
from a finite principal refinement and the actual localization calculation.
No Čech exactness, local-lift, or H¹-vanishing premise remains. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.ActualAffineH1

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Cylinder.ActualAffineCechOne Cylinder.SheafInjectiveCokernel

variable (R : Type u) [CommRing R]

theorem enough_injectives : EnoughInjectives (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u}) := inferInstance

theorem has_ext : HasExt.{u} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u}) := inferInstance

variable [IsDomain R]

theorem lift_section
    {S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (e : S.X₁ ≅ structureAb R)
    (t : S.X₃.obj.obj (op (⊤ : Opens (PrimeSpectrum.Top R)))) :
    ∃ a : S.X₂.obj.obj (op (⊤ : Opens (PrimeSpectrum.Top R))), S.g.hom.app (op ⊤) a = t :=
  Cylinder.ActualAffineSectionsLift.lift_section (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R)) hS e t

theorem cohomologyOne_subsingleton : Subsingleton (CategoryTheory.Sheaf.H (structureAb R) 1) := by
  have hS := injectiveSequence_shortExact (structureAb R)
  let : Subsingleton (CategoryTheory.Sheaf.H (injectiveSequence (structureAb R)).X₂ 1) :=
    injective_cohomologyOne_subsingleton (Injective.under (structureAb R))
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  obtain ⟨s, hs⟩ := Cylinder.SheafCohomologyCokernel.sectionConnecting_surjective hS isTerminalTop x
  obtain ⟨a, ha⟩ := lift_section R hS (Iso.refl _) s
  rw [← hs, ← ha]
  exact Cylinder.SheafCohomologyCokernel.sectionConnecting_map_zero hS isTerminalTop a

theorem cohomologyOne_eq_zero (x : CategoryTheory.Sheaf.H (structureAb R) 1) : x = 0 :=
  (cohomologyOne_subsingleton R).elim x 0

end Cylinder.ActualAffineH1

end
