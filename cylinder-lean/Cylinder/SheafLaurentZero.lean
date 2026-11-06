module

public import Cylinder.SheafZeroCocycles
public import Cylinder.PlaneLaurentHomogeneous

/-! A gluing bridge for an actual sheaf whose chart-section diagram has
been identified with the Laurent diagram. The local identifications and
their compatibility are explicit inputs; no global-section formula or
cohomology vanishing is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.SheafLaurentZero

open CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.SheafZeroCocycles Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentCech

universe u
variable (K : Type u) [CommRing K]

def tripleEquiv (M : Fin 3 → ModuleCat.{u} K) :
    (∀ i, M i) ≃ₗ[K] M 0 × M 1 × M 2 where
  toFun s := (s 0, s 1, s 2)
  invFun s := Fin.cases s.1 (Fin.cases s.2.1 (Fin.cases s.2.2 (fun i => Fin.elim0 i)))
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv s := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (X : TopCat.{u})
    (F : TopCat.Sheaf (ModuleCat.{u} K) X) (U : Fin 3 → Opens X) (v : ℤ)
    (e : (∀ i, F.obj.obj (op (U i))) ≃ₗ[K] ZeroCochains (K := K) v)
    (he : ∀ s, TopCat.Presheaf.IsCompatible F.obj U s ↔ differentialZero v (e s) = 0)

def compatibleEquivKernel : compatibleSections K X F U ≃ₗ[K]
    LinearMap.ker (differentialZero (K := K) v) where
  toFun s := ⟨e s.val, (he s.val).mp s.property⟩
  invFun s := ⟨e.symm s.val, (he (e.symm s.val)).mpr (by
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp s.property)⟩
  left_inv s := Subtype.ext (e.symm_apply_apply s.val)
  right_inv s := Subtype.ext (e.apply_symm_apply s.val)
  map_add' s t := Subtype.ext (e.map_add s.val t.val)
  map_smul' a s := Subtype.ext (e.map_smul a s.val)

def globalSectionsEquivForms (hcover : (⊤ : Opens X) ≤ iSup U) :
    F.obj.obj (op ⊤) ≃ₗ[K] PlaneLaurentHomogeneous.integerForms K v :=
  (SheafZeroCocycles.globalSectionsEquiv K X F U hcover).trans
    ((compatibleEquivKernel K X F U v e he).trans
      (PlaneLaurentHomogeneous.kernelEquivForms K v))

include e he in
theorem globalSections_zero_of_negative (hcover : (⊤ : Opens X) ≤ iSup U)
    (hv : v < 0) (s : F.obj.obj (op ⊤)) : s = 0 := by
  apply (globalSectionsEquivForms K X F U v e he hcover).injective
  rw [map_zero]
  apply Subtype.ext
  have hbot : PlaneLaurentHomogeneous.integerForms K v = ⊥ := by
    simp only [PlaneLaurentHomogeneous.integerForms, ite_eq_right (not_le.mpr hv)]
  exact (Submodule.mem_bot K).mp (hbot ▸
    (globalSectionsEquivForms K X F U v e he hcover s).property)

end Cylinder.SheafLaurentZero
end
