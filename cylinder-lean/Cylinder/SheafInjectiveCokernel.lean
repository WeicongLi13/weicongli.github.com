module

public import Cylinder.SheafCohomologyCokernel
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! A genuine injective-cokernel model for Ext-defined sheaf H¹.
The vanishing of the injective middle term is proved by Ext, rather
than supplied as an additional cohomology hypothesis. -/

@[expose] public section
noncomputable section

universe w' w v u

namespace Cylinder.SheafInjectiveCokernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

def cokernelSequence {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

omit [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] in
theorem cokernelSequence_shortExact {F I : Sheaf J AddCommGrpCat.{w}}
    (i : F ⟶ I) [Mono i] : (cokernelSequence i).ShortExact := by
  unfold cokernelSequence
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }

theorem injective_cohomologyOne_subsingleton (I : Sheaf J AddCommGrpCat.{w}) [Injective I] :
    Subsingleton (Sheaf.H I 1) :=
  CategoryTheory.Abelian.Ext.subsingleton_of_injective _ I 0

abbrev globalSectionsToCokernel {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) (T : C) :
    I.obj.obj (op T) →+ (cokernel i).obj.obj (op T) :=
  ((cokernel.π i).hom.app (op T)).hom

def cohomologyOneEquivCokernel {F I : Sheaf J AddCommGrpCat.{w}}
    (i : F ⟶ I) [Mono i] [Injective I] {T : C} (hT : IsTerminal T) :
    Sheaf.H F 1 ≃+
      ((cokernel i).obj.obj (op T) ⧸ (globalSectionsToCokernel i T).range) := by
  let : Subsingleton (Sheaf.H (cokernelSequence i).X₂ 1) :=
    injective_cohomologyOne_subsingleton I
  exact (Cylinder.SheafCohomologyCokernel.globalSectionsCokernelEquiv
    (cokernelSequence_shortExact i) hT).symm

theorem cohomologyOneEquivCokernel_symm_mk {F I : Sheaf J AddCommGrpCat.{w}}
    (i : F ⟶ I) [Mono i] [Injective I] {T : C} (hT : IsTerminal T)
    (x : (cokernel i).obj.obj (op T)) :
    (cohomologyOneEquivCokernel i hT).symm (QuotientAddGroup.mk x) =
      Cylinder.SheafCohomologyCokernel.sectionConnecting (cokernelSequence_shortExact i) hT x := by
  let : Subsingleton (Sheaf.H (cokernelSequence i).X₂ 1) :=
    injective_cohomologyOne_subsingleton I
  change (Cylinder.SheafCohomologyCokernel.globalSectionsCokernelEquiv
    (cokernelSequence_shortExact i) hT) (QuotientAddGroup.mk x) = _
  simp only [Cylinder.SheafCohomologyCokernel.globalSectionsCokernelEquiv,
    AddEquiv.trans_apply]
  rfl

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- The chosen embedding is an actual monomorphism into an injective
sheaf supplied by the category's enough-injectives structure. -/
abbrev injectiveSequence (F : Sheaf J AddCommGrpCat.{w}) :=
  cokernelSequence (Injective.ι F)

omit [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] in
theorem injectiveSequence_shortExact (F : Sheaf J AddCommGrpCat.{w}) :
    (injectiveSequence F).ShortExact := cokernelSequence_shortExact (Injective.ι F)

def injectiveCohomologyOneEquiv (F : Sheaf J AddCommGrpCat.{w}) {T : C} (hT : IsTerminal T) :
    Sheaf.H F 1 ≃+
      ((cokernel (Injective.ι F)).obj.obj (op T) ⧸
        (globalSectionsToCokernel (Injective.ι F) T).range) :=
  cohomologyOneEquivCokernel (Injective.ι F) hT

end Cylinder.SheafInjectiveCokernel

end
