module

public import Cylinder.ActualAffineH1
public import Cylinder.SheafOpenRestrictionExact

/-! Actual local section lifts along an affine open embedding.
This applies an arbitrary global short exact sequence to an affine chart.
Only its actual kernel trivialization on that chart is required; no
preservation of injective objects, section surjectivity, or H¹ premise occurs. -/

@[expose] public section
noncomputable section

universe u

namespace Cylinder.ActualAffineOpenEmbeddingLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.ActualAffineCechOne

variable {X Y : TopCat.{u}} {f : X ⟶ Y}

def pullback (hf : Topology.IsOpenEmbedding f) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hf.sheafPullback AddCommGrpCat.{u}

instance pullback_additive (hf : Topology.IsOpenEmbedding f) :
    (pullback hf).Additive where
  map_add := by intros; rfl

instance pullback_preservesZeroMorphisms (hf : Topology.IsOpenEmbedding f) :
    (pullback hf).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩

instance pullback_preservesFiniteLimits (hf : Topology.IsOpenEmbedding f) :
    PreservesFiniteLimits (pullback hf) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := hf.functor_isContinuous
  change PreservesFiniteLimits (hf.functor.sheafPushforwardContinuous AddCommGrpCat.{u} _ _)
  infer_instance

instance pullback_preservesFiniteColimits (hf : Topology.IsOpenEmbedding f) :
    PreservesFiniteColimits (pullback hf) := by
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (hf.sheafPullbackIso AddCommGrpCat.{u})
    ⟨fun J _ _ =>
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩

abbrev pullbackComplex (hf : Topology.IsOpenEmbedding f)
    (S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})) :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  letI : (pullback hf).PreservesZeroMorphisms :=
    pullback_preservesZeroMorphisms hf
  exact S.map (pullback hf)

theorem pullback_shortExact (hf : Topology.IsOpenEmbedding f)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) : (pullbackComplex hf S).ShortExact := by
  let : (pullback hf).PreservesZeroMorphisms :=
    pullback_preservesZeroMorphisms hf
  let : PreservesFiniteLimits (pullback hf) :=
    pullback_preservesFiniteLimits hf
  let : PreservesFiniteColimits (pullback hf) :=
    pullback_preservesFiniteColimits hf
  exact hS.map_of_exact (pullback hf)

theorem lift_section (R : Type u) [CommRing R] [IsDomain R]
    {X : TopCat.{u}} (f : PrimeSpectrum.Top R ⟶ X) (hf : Topology.IsOpenEmbedding f)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact)
    (e : (pullback hf).obj S.X₁ ≅ structureAb R)
    (t : S.X₃.obj.obj (op (hf.functor.obj (⊤ : Opens (PrimeSpectrum.Top R))))) :
    ∃ a : S.X₂.obj.obj (op (hf.functor.obj (⊤ : Opens (PrimeSpectrum.Top R)))),
      S.g.hom.app (op (hf.functor.obj ⊤)) a = t := by
  change ∃ a : ((pullback hf).obj S.X₂).obj.obj
      (op (⊤ : Opens (PrimeSpectrum.Top R))),
    ((pullback hf).map S.g).hom.app (op ⊤) a = t
  exact Cylinder.ActualAffineH1.lift_section R (pullback_shortExact hf hS) e t

theorem sections_surjective (R : Type u) [CommRing R] [IsDomain R]
    {X : TopCat.{u}} (f : PrimeSpectrum.Top R ⟶ X) (hf : Topology.IsOpenEmbedding f)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact)
    (e : (pullback hf).obj S.X₁ ≅ structureAb R) :
    Function.Surjective (S.g.hom.app (op (hf.functor.obj (⊤ : Opens (PrimeSpectrum.Top R))))) :=
  fun t => lift_section R f hf hS e t

end Cylinder.ActualAffineOpenEmbeddingLift

end
