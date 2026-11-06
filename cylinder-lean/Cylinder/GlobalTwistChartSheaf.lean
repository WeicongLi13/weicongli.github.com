module

public import Cylinder.GlobalTwistChartFrame

/-! The coordinate frames identify the actual restriction of the global
twisting sheaf with the actual structure module on each standard chart. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistChartSheaf

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame

variable (K : Type*) [Field K]

abbrev structureModule : (plane K).Modules :=
  SheafOfModules.unit (plane K).ringCatSheaf

def restrictedSectionEquiv (i : Option (Fin 2)) (v : ℤ)
    (U : (coordinateOpen K i).toScheme.Opens) :
    Γ((structureModule K).restrict (coordinateOpen K i).ι, U)
      ≃ₗ[Γ((coordinateOpen K i).toScheme, U)]
        Γ((twist K v).restrict (coordinateOpen K i).ι, U) :=
  { __ := (chartSectionEquiv K i v ((coordinateOpen K i).ι ''ᵁ U)
      ((coordinateOpen K i).ι_image_le U)).toAddEquiv
    map_smul' := by
      intro r s
      change Γ(plane K, (coordinateOpen K i).ι ''ᵁ U) at s
      change chartSectionEquiv K i v ((coordinateOpen K i).ι ''ᵁ U) _
          (((coordinateOpen K i).ι.appIso U).inv r * s) =
        ((coordinateOpen K i).ι.appIso U).inv r •
          chartSectionEquiv K i v ((coordinateOpen K i).ι ''ᵁ U) _ s
      exact (chartSectionEquiv K i v ((coordinateOpen K i).ι ''ᵁ U)
        ((coordinateOpen K i).ι_image_le U)).map_smul _ _ }

def restrictedPresheafIso (i : Option (Fin 2)) (v : ℤ) :
    ((structureModule K).restrict (coordinateOpen K i).ι).val ≅
      ((twist K v).restrict (coordinateOpen K i).ι).val :=
  PresheafOfModules.isoMk
    (fun U => (restrictedSectionEquiv K i v U.unop).toModuleIso)
    (by intro U V j; rfl)

def restrictedFrameIso (i : Option (Fin 2)) (v : ℤ) :
    (structureModule K).restrict (coordinateOpen K i).ι ≅
      (twist K v).restrict (coordinateOpen K i).ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (restrictedPresheafIso K i v)

def chartTrivialization (i : Option (Fin 2)) (v : ℤ) :
    (twist K v).restrict (coordinateOpen K i).ι ≅
      SheafOfModules.unit (coordinateOpen K i).toScheme.ringCatSheaf :=
  (restrictedFrameIso K i v).symm ≪≫
    Scheme.Modules.restrictUnitIso (coordinateOpen K i).ι

theorem restrictedFrameIso_apply (i : Option (Fin 2)) (v : ℤ)
    (U : (coordinateOpen K i).toScheme.Opens)
    (s : Γ((structureModule K).restrict (coordinateOpen K i).ι, U))
    (q : (coordinateOpen K i).ι ''ᵁ U) :
    (((restrictedFrameIso K i v).hom.app U) s).val q =
      (frame K i v ((coordinateOpen K i).ι ''ᵁ U) ((coordinateOpen K i).ι_image_le U)).val q *
        (s.val q).val := rfl

end Cylinder.GlobalTwistChartSheaf
end
