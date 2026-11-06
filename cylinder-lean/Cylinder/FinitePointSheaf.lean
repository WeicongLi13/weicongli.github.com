module

public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual sheaf supported on a family of points, with one copy
of the coefficient field at each point. Its global sections are computed
from the genuine product of skyscraper sheaves. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.FinitePointSheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u
variable (K : Type u) [CommRing K] (X : TopCat.{u}) {I : Type u}

def pointSheaf (x : X) : TopCat.Sheaf (ModuleCat.{u} K) X :=
  skyscraperSheaf x (ModuleCat.of K K)

def supportedSheaf (x : I → X) : TopCat.Sheaf (ModuleCat.{u} K) X :=
  ∏ᶜ fun i => pointSheaf K X (x i)

def sectionsFunctor (U : Opens X) : TopCat.Sheaf (ModuleCat.{u} K) X ⥤ ModuleCat.{u} K :=
  TopCat.Sheaf.forget (ModuleCat.{u} K) X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} K)).obj (op U)

instance sectionsFunctor_preservesLimits (U : Opens X) :
    PreservesLimitsOfSize.{u, u} (sectionsFunctor K X U) where
  preservesLimitsOfShape {J} instJ := by
    letI := instJ
    haveI : PreservesLimitsOfShape J
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} K)) := inferInstance
    haveI : PreservesLimitsOfShape J
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} K)).obj (op U)) := inferInstance
    dsimp only [sectionsFunctor, TopCat.Sheaf.forget]
    infer_instance

def pointGlobalSectionsIso (x : X) :
    (pointSheaf K X x).obj.obj (op ⊤) ≅ ModuleCat.of K K := by
  apply eqToIso
  change (if x ∈ (⊤ : Opens X) then ModuleCat.of K K else terminal (ModuleCat.{u} K)) = _
  simp

def globalSectionsIso (x : I → X) :
    (supportedSheaf K X x).obj.obj (op ⊤) ≅ ModuleCat.of K (I → K) :=
  (PreservesProduct.iso (sectionsFunctor K X ⊤) (fun i => pointSheaf K X (x i))) ≪≫
    Pi.mapIso (fun i => pointGlobalSectionsIso K X (x i)) ≪≫
      ModuleCat.piIsoPi (fun _ : I => ModuleCat.of K K)

def globalSectionsLinearEquiv (x : I → X) :
    (supportedSheaf K X x).obj.obj (op ⊤) ≃ₗ[K] (I → K) :=
  (globalSectionsIso K X x).toLinearEquiv

theorem globalSections_finrank {L : Type u} [Field L] [Fintype I] (x : I → X) :
    Module.finrank L ((supportedSheaf L X x).obj.obj (op ⊤)) = Fintype.card I := by
  rw [(globalSectionsLinearEquiv L X x).finrank_eq, Module.finrank_fintype_fun_eq_card]

end Cylinder.FinitePointSheaf
end
