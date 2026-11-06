module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The cokernel of the actual global-section map is the first
sheaf-cohomology group when the middle sheaf has vanishing H¹.
Here `Sheaf.H` is mathlib's Ext-defined sheaf cohomology, not a
renaming of a numerical evaluation defect.  The application to the
twisted ideal sheaf on projective space is a separate construction. -/

@[expose] public section
noncomputable section

universe w' w v u

namespace Cylinder.SheafCohomologyCokernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
  {T : C} (hT : IsTerminal T)

abbrev globalSectionsMap : S.X₂.obj.obj (op T) →+ S.X₃.obj.obj (op T) :=
  (S.g.hom.app (op T)).hom

def sectionConnecting : S.X₃.obj.obj (op T) →+ Sheaf.H S.X₁ 1 :=
  (Sheaf.H.δ hS 0 1 rfl).comp (Sheaf.H.equiv₀ S.X₃ hT).symm.toAddMonoidHom

theorem connecting_map_zero (x : Sheaf.H S.X₂ 0) :
    Sheaf.H.δ hS 0 1 rfl (Sheaf.H.map S.g 0 x) = 0 := by
  have hz : AddCommGrpCat.ofHom (Sheaf.H.map S.g 0) ≫
      AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl) = 0 :=
    (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
  exact congrArg (fun f : AddCommGrpCat.of (Sheaf.H S.X₂ 0) ⟶
    AddCommGrpCat.of (Sheaf.H S.X₁ 1) => f x) hz

theorem sectionConnecting_map_zero (x : S.X₂.obj.obj (op T)) :
    sectionConnecting hS hT (globalSectionsMap (S := S) x) = 0 := by
  change Sheaf.H.δ hS 0 1 rfl
    ((Sheaf.H.equiv₀ S.X₃ hT).symm ((S.g.hom.app (op T)) x)) = 0
  rw [← Sheaf.H.equiv₀_symm_naturality (f := S.g) hT]
  exact connecting_map_zero hS _

theorem sectionConnecting_ker :
    (sectionConnecting hS hT).ker = (globalSectionsMap (S := S) (T := T)).range := by
  ext x
  change sectionConnecting hS hT x = 0 ↔ ∃ y, globalSectionsMap (S := S) y = x
  constructor
  · intro hx
    exact Sheaf.H.longSequence_equiv₀_exact₃ hS hT x hx
  · rintro ⟨y, rfl⟩
    exact sectionConnecting_map_zero hS hT y

theorem sectionConnecting_surjective [Subsingleton (Sheaf.H S.X₂ 1)] :
    Function.Surjective (sectionConnecting hS hT) := by
  intro x
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
  refine ⟨Sheaf.H.equiv₀ S.X₃ hT y, ?_⟩
  change Sheaf.H.δ hS 0 1 rfl
    ((Sheaf.H.equiv₀ S.X₃ hT).symm (Sheaf.H.equiv₀ S.X₃ hT y)) = x
  rwa [AddEquiv.symm_apply_apply]

def globalSectionsCokernelEquiv [Subsingleton (Sheaf.H S.X₂ 1)] :
    S.X₃.obj.obj (op T) ⧸ (globalSectionsMap (S := S) (T := T)).range ≃+
      Sheaf.H S.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (sectionConnecting_ker hS hT).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (sectionConnecting hS hT)
      (sectionConnecting_surjective hS hT))

end Cylinder.SheafCohomologyCokernel

end
