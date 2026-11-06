module

public import Cylinder.SheafCechOneDescent

/-! Transport of actual Čech one-cocycles along an actual sheaf isomorphism. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.SheafCechOneIsomorphism

open CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.SheafCechOneDescent

variable {X : TopCat.{u}}
  {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

def sectionsEquiv (e : F ≅ G) (V : Opens X) : F.obj.obj (op V) ≃+ G.obj.obj (op V) :=
  (((CategoryTheory.sheafToPresheaf _ _).mapIso e).app (op V)).addCommGroupIsoToAddEquiv

theorem cech_one_exact_of_iso {I : Type*} (e : F ≅ G) (U : I → Opens X)
    (hG : CechOneExact G U) : CechOneExact F U := by
  intro z hz
  let w (i j : I) := e.hom.hom.app (op (U i ⊓ U j)) (z i j)
  have hw (i j k : I) :
      sectionsRestrict G (inf_le_inf inf_le_left le_rfl) (w i k) -
        sectionsRestrict G (inf_le_inf inf_le_right le_rfl) (w j k) =
      sectionsRestrict G inf_le_left (w i j) := by
    have h := congrArg (fun x => e.hom.hom.app (op (U i ⊓ U j ⊓ U k)) x) (hz i j k)
    simpa only [map_sub, map_sectionsRestrict e.hom, w] using h
  obtain ⟨c, hc⟩ := hG w hw
  have hi (V : Opens X) (x : G.obj.obj (op V)) :
      e.hom.hom.app (op V) (e.inv.hom.app (op V) x) = x :=
    congrArg (fun f : G ⟶ G => f.hom.app (op V) x) e.inv_hom_id
  refine ⟨fun i => e.inv.hom.app (op (U i)) (c i), fun i j => ?_⟩
  apply (sectionsEquiv e (U i ⊓ U j)).injective
  change e.hom.hom.app (op (U i ⊓ U j))
      (sectionsRestrict F inf_le_left (e.inv.hom.app (op (U i)) (c i)) -
        sectionsRestrict F inf_le_right (e.inv.hom.app (op (U j)) (c j))) =
      e.hom.hom.app (op (U i ⊓ U j)) (z i j)
  simp only [map_sub, map_sectionsRestrict e.hom, hi]
  exact hc i j

theorem cech_one_exact_iff_of_iso {I : Type*} (e : F ≅ G) (U : I → Opens X) :
    CechOneExact F U ↔ CechOneExact G U :=
  ⟨cech_one_exact_of_iso e.symm U, cech_one_exact_of_iso e U⟩

end Cylinder.SheafCechOneIsomorphism

end
