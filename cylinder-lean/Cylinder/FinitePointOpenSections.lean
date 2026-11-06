module

public import Cylinder.FinitePointSheaf

/-! Actual sections of a finite-point product on opens containing all
points, and their vanishing on opens containing none of the points. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.FinitePointOpenSections

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Cylinder.FinitePointSheaf

universe u
variable (K : Type u) [CommRing K] (X : TopCat.{u}) {I : Type u}

def pointSectionsIso (x : X) (U : Opens X) (hx : x ∈ U) :
    (pointSheaf K X x).obj.obj (op U) ≅ ModuleCat.of K K :=
  eqToIso (by change (if x ∈ U then ModuleCat.of K K else terminal (ModuleCat K)) = _
              simp only [ite_eq_left hx])

def sectionsIso (x : I → X) (U : Opens X) (hx : ∀ i, x i ∈ U) :
    (supportedSheaf K X x).obj.obj (op U) ≅ ModuleCat.of K (I → K) :=
  PreservesProduct.iso (sectionsFunctor K X U) (fun i => pointSheaf K X (x i)) ≪≫
    Pi.mapIso (fun i => pointSectionsIso K X (x i) U (hx i)) ≪≫
      ModuleCat.piIsoPi (fun _ : I => ModuleCat.of K K)

def sectionsLinearEquiv (x : I → X) (U : Opens X) (hx : ∀ i, x i ∈ U) :
    (supportedSheaf K X x).obj.obj (op U) ≃ₗ[K] (I → K) :=
  (sectionsIso K X x U hx).toLinearEquiv

theorem sectionsIso_projection (x : I → X) (U : Opens X) (hx : ∀ i, x i ∈ U) (i : I) :
    (sectionsIso K X x U hx).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (I → K) →ₗ[K] K) =
    (sectionsFunctor K X U).map (Pi.π (fun j => pointSheaf K X (x j)) i) ≫
      (pointSectionsIso K X (x i) U (hx i)).hom := by
  dsimp only [sectionsIso]
  simp only [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
    Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc]

theorem sectionsLinearEquiv_apply (x : I → X) (U : Opens X) (hx : ∀ i, x i ∈ U)
    (s : (supportedSheaf K X x).obj.obj (op U)) (i : I) :
    sectionsLinearEquiv K X x U hx s i =
      (pointSectionsIso K X (x i) U (hx i)).hom
        ((Pi.π (fun j => pointSheaf K X (x j)) i).hom.app (op U) s) :=
  ConcreteCategory.congr_hom (sectionsIso_projection K X x U hx i) s

theorem sections_subsingleton_of_not_mem (x : I → X) (U : Opens X)
    (hx : ∀ i, x i ∉ U) : Subsingleton ((supportedSheaf K X x).obj.obj (op U)) := by
  have hi (i : I) : Subsingleton ((pointSheaf K X (x i)).obj.obj (op U)) :=
    ModuleCat.subsingleton_of_isZero
      (isTerminalSkyscraperSheafObjObjOfNotMem (A := ModuleCat.of K K) (hx i)).isZero
  letI := hi
  let e := PreservesProduct.iso (sectionsFunctor K X U) (fun i => pointSheaf K X (x i)) ≪≫
    ModuleCat.piIsoPi (fun i => (pointSheaf K X (x i)).obj.obj (op U))
  exact ⟨fun a b => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

end Cylinder.FinitePointOpenSections
end
