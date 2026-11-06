module

public import Cylinder.FinitePointSheaf

/-! The coordinate maps of the actual global-section product isomorphism. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.FinitePointSheafProjections

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Cylinder.FinitePointSheaf

universe u
variable (K : Type u) [CommRing K] (X : TopCat.{u}) {I : Type u}

theorem globalSectionsIso_projection (x : I → X) (i : I) :
    (globalSectionsIso K X x).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (I → K) →ₗ[K] K) =
    (sectionsFunctor K X ⊤).map (Pi.π (fun j => pointSheaf K X (x j)) i) ≫
      (pointGlobalSectionsIso K X (x i)).hom := by
  dsimp only [globalSectionsIso]
  simp only [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
    Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc]

theorem globalSectionsLinearEquiv_apply (x : I → X)
    (s : (supportedSheaf K X x).obj.obj (op ⊤)) (i : I) :
    globalSectionsLinearEquiv K X x s i =
      (pointGlobalSectionsIso K X (x i)).hom
        ((Pi.π (fun j => pointSheaf K X (x j)) i).hom.app (op ⊤) s) := by
  exact ConcreteCategory.congr_hom (globalSectionsIso_projection K X x i) s

end Cylinder.FinitePointSheafProjections
end
