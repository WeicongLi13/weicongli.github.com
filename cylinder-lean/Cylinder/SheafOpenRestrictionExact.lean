module

public import Cylinder.SheafCechOneDescent
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual open restriction of additive sheaves preserves short exact sequences.
Finite colimits are transferred from the true inverse-image left adjoint
through its proved isomorphism with image-open restriction.  No preservation
of injective objects is asserted or required. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.SheafOpenRestrictionExact

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.SheafCechOneDescent

variable {X : TopCat.{u}}

instance restriction_additive (U : Opens X) :
    (U.sheafRestrict (C := AddCommGrpCat.{u})).Additive where
  map_add := by intros; rfl

instance restriction_preservesFiniteColimits (U : Opens X) :
    PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
  let f : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hf : Topology.IsOpenEmbedding f := U.isOpenEmbedding
  have e : TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
      U.sheafRestrict (C := AddCommGrpCat.{u}) := hf.sheafPullbackIso _
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _ e
    ⟨fun J _ _ =>
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

theorem restriction_shortExact
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (U : Opens X) :
    (S.map (U.sheafRestrict (C := AddCommGrpCat.{u}))).ShortExact :=
  hS.map_of_exact _

def topSectionsEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : Opens X) :
    ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F).obj.obj (op (⊤ : Opens U)) ≃+
      F.obj.obj (op U) :=
  (F.obj.mapIso (eqToIso U.isOpenEmbedding_obj_top.symm).op).addCommGroupIsoToAddEquiv

theorem topSectionsEquiv_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (U : Opens X)
    (x : ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F).obj.obj (op (⊤ : Opens U))) :
    topSectionsEquiv G U (((U.sheafRestrict (C := AddCommGrpCat.{u})).map f).hom.app (op ⊤) x) =
      f.hom.app (op U) (topSectionsEquiv F U x) := by
  change sectionsRestrict G U.isOpenEmbedding_obj_top.ge
      (f.hom.app _ x) = f.hom.app _ (sectionsRestrict F U.isOpenEmbedding_obj_top.ge x)
  exact (map_sectionsRestrict f U.isOpenEmbedding_obj_top.ge x).symm

theorem lift_section_of_restricted_lift
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (U : Opens X) (t : S.X₃.obj.obj (op U))
    (a : ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj S.X₂).obj.obj (op (⊤ : Opens U)))
    (ha : ((U.sheafRestrict (C := AddCommGrpCat.{u})).map S.g).hom.app (op ⊤) a =
      (topSectionsEquiv S.X₃ U).symm t) :
    ∃ x : S.X₂.obj.obj (op U), S.g.hom.app (op U) x = t := by
  refine ⟨topSectionsEquiv S.X₂ U a, ?_⟩
  rw [← topSectionsEquiv_naturality, ha, AddEquiv.apply_symm_apply]

end Cylinder.SheafOpenRestrictionExact

end
