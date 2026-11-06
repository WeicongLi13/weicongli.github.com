module

public import Cylinder.FinitePointSheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual global sections of a sheaf of K-modules are naturally the
compatible families of sections on any open cover. This uses the genuine
sheaf gluing axiom and has no cohomological vanishing assumption. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.SheafZeroCocycles

open CategoryTheory TopCat TopologicalSpace Opposite

universe u
variable (K : Type u) [CommRing K] (X : TopCat.{u})
    (F : TopCat.Sheaf (ModuleCat.{u} K) X) {I : Type*} (U : I → Opens X)

def compatibleSections : Submodule K (∀ i, F.obj.obj (op (U i))) where
  carrier s := TopCat.Presheaf.IsCompatible F.obj U s
  zero_mem' := by
    intro i j
    change F.obj.map _ 0 = F.obj.map _ 0
    simp
  add_mem' := by
    intro s t hs ht i j
    change F.obj.map _ (s i + t i) = F.obj.map _ (s j + t j)
    rw [map_add, map_add, hs i j, ht i j]
  smul_mem' := by
    intro a s hs i j
    change F.obj.map _ (a • s i) = F.obj.map _ (a • s j)
    rw [map_smul, map_smul, hs i j]

def globalRestriction : F.obj.obj (op ⊤) →ₗ[K] compatibleSections K X F U where
  toFun s := ⟨fun i => F.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op s, by
    intro i j
    simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    rfl⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _
  map_smul' a s := by
    apply Subtype.ext
    funext i
    exact map_smul _ _ _

theorem globalRestriction_apply (s : F.obj.obj (op ⊤)) (i : I) :
    (globalRestriction K X F U s).val i = F.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op s := rfl

theorem globalRestriction_injective (hcover : (⊤ : Opens X) ≤ iSup U) :
    Function.Injective (globalRestriction K X F U) := by
  intro s t h
  apply F.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hcover s t
  intro i
  exact congrArg (fun z : compatibleSections K X F U => z.val i) h

theorem globalRestriction_surjective (hcover : (⊤ : Opens X) ≤ iSup U) :
    Function.Surjective (globalRestriction K X F U) := by
  intro z
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top)
    hcover z.val z.property
  exact ⟨s, Subtype.ext (funext hs)⟩

def globalSectionsEquiv (hcover : (⊤ : Opens X) ≤ iSup U) :
    F.obj.obj (op ⊤) ≃ₗ[K] compatibleSections K X F U :=
  LinearEquiv.ofBijective (globalRestriction K X F U)
    ⟨globalRestriction_injective K X F U hcover, globalRestriction_surjective K X F U hcover⟩

theorem globalSectionsEquiv_apply (hcover : (⊤ : Opens X) ≤ iSup U)
    (s : F.obj.obj (op ⊤)) (i : I) :
    (globalSectionsEquiv K X F U hcover s).val i =
      F.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op s := rfl

end Cylinder.SheafZeroCocycles
end
