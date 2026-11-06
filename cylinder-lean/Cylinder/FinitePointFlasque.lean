module

public import Cylinder.FinitePointSheaf
public import Mathlib.Topology.Sheaves.Flasque

/-! Restriction maps of the actual product of skyscraper sheaves are
surjective. The proof uses the genuine pointwise product comparison. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.FinitePointFlasque

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open Cylinder.FinitePointSheaf

universe u
variable (K : Type u) [CommRing K] (X : TopCat.{u}) {I : Type u}

def rawSectionsIso (x : I → X) (U : Opens X) :
    (supportedSheaf K X x).obj.obj (op U) ≅
      ModuleCat.of K (∀ i, (pointSheaf K X (x i)).obj.obj (op U)) :=
  PreservesProduct.iso (sectionsFunctor K X U) (fun i => pointSheaf K X (x i)) ≪≫
    ModuleCat.piIsoPi (fun i => (pointSheaf K X (x i)).obj.obj (op U))

def rawSectionsLinearEquiv (x : I → X) (U : Opens X) :
    (supportedSheaf K X x).obj.obj (op U) ≃ₗ[K]
      (∀ i, (pointSheaf K X (x i)).obj.obj (op U)) :=
  (rawSectionsIso K X x U).toLinearEquiv

theorem rawSectionsIso_projection (x : I → X) (U : Opens X) (i : I) :
    (rawSectionsIso K X x U).hom ≫ ModuleCat.ofHom
      (LinearMap.proj i : (∀ j, (pointSheaf K X (x j)).obj.obj (op U)) →ₗ[K]
        (pointSheaf K X (x i)).obj.obj (op U)) =
    (sectionsFunctor K X U).map (Pi.π (fun j => pointSheaf K X (x j)) i) := by
  dsimp only [rawSectionsIso]
  simp only [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
    PreservesProduct.iso_hom]
  exact piComparison_comp_π _ _ i

theorem rawSectionsLinearEquiv_apply (x : I → X) (U : Opens X)
    (s : (supportedSheaf K X x).obj.obj (op U)) (i : I) :
    rawSectionsLinearEquiv K X x U s i =
      (Pi.π (fun j => pointSheaf K X (x j)) i).hom.app (op U) s :=
  ConcreteCategory.congr_hom (rawSectionsIso_projection K X x U i) s

theorem rawSections_restrict (x : I → X) {U V : Opens X} (i : U ⟶ V)
    (s : (supportedSheaf K X x).obj.obj (op V)) (j : I) :
    rawSectionsLinearEquiv K X x U ((supportedSheaf K X x).obj.map i.op s) j =
      (pointSheaf K X (x j)).obj.map i.op (rawSectionsLinearEquiv K X x V s j) := by
  rw [rawSectionsLinearEquiv_apply, rawSectionsLinearEquiv_apply]
  exact ConcreteCategory.congr_hom
    ((Pi.π (fun k => pointSheaf K X (x k)) j).hom.naturality i.op) s

theorem restrictions_surjective (x : I → X) {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective ((supportedSheaf K X x).obj.map i.op) := by
  letI (j : I) : TopCat.Sheaf.IsFlasque (pointSheaf K X (x j)) :=
    isFlasque_skyscraperSheaf_of_hasZeroObject (x j) (ModuleCat.of K K)
  have hsurj (j : I) : Function.Surjective ((pointSheaf K X (x j)).obj.map i.op) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  intro t
  choose a ha using fun j => hsurj j (rawSectionsLinearEquiv K X x U t j)
  refine ⟨(rawSectionsLinearEquiv K X x V).symm a,
    (rawSectionsLinearEquiv K X x U).injective ?_⟩
  funext j
  rw [rawSections_restrict, LinearEquiv.apply_symm_apply]
  exact ha j

end Cylinder.FinitePointFlasque
end
