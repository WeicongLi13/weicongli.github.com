module

public import Cylinder.ActualAffineCechOne
public import Cylinder.AffineFiniteBasicCover
public import Cylinder.SheafCechOneIsomorphism

/-! Global lifts on an actual affine spectrum for a structure-sheaf kernel.
The principal cover and its local lifts are derived from the actual epimorphism.
Its Čech exactness is proved by concrete localizations and clearing denominators.
No cohomological vanishing, covering, or local lifting hypothesis is used. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.ActualAffineSectionsLift

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.ActualAffineCechOne Cylinder.AffineFiniteBasicCover
open Cylinder.SheafCechOneDescent Cylinder.SheafCechOneIsomorphism

variable {R K : Type u} [CommRing R] [Field K]

theorem lift_section
    (ι : R →+* K) (hι : Function.Injective ι)
    {S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (e : S.X₁ ≅ structureAb R)
    (t : S.X₃.obj.obj (op (⊤ : Opens (PrimeSpectrum.Top R)))) :
    ∃ a : S.X₂.obj.obj (op (⊤ : Opens (PrimeSpectrum.Top R))), S.g.hom.app (op ⊤) a = t := by
  obtain ⟨J, hJ, f, hf0, hspan, s, hs⟩ :=
    @exists_finite_basic_lifting_cover R _ S.X₂ S.X₃ S.g hS.epi_g t
  let := hJ
  have hf (j : J) : ι (f j) ≠ 0 := fun h => hf0 j (hι (h.trans (map_zero ι).symm))
  have hcech : CechOneExact S.X₁ (fun j => PrimeSpectrum.basicOpen (f j)) :=
    cech_one_exact_of_iso e _ (structureAb_cech_one_exact ι hι f hf hspan)
  have hcover : (⊤ : Opens (PrimeSpectrum.Top R)) ≤
      iSup (fun j => PrimeSpectrum.basicOpen (f j)) :=
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan).ge
  exact lift_section_of_cech_one_exact hS _ hcover hcech t s hs

theorem sections_surjective
    (ι : R →+* K) (hι : Function.Injective ι)
    {S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (PrimeSpectrum.Top R)) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (e : S.X₁ ≅ structureAb R) :
    Function.Surjective (S.g.hom.app (op (⊤ : Opens (PrimeSpectrum.Top R)))) :=
  fun t => lift_section ι hι hS e t

end Cylinder.ActualAffineSectionsLift

end
