module

public import Cylinder.GlobalTwistLocalFractions

/-! A global sheaf of degree-v homogeneous fractions on the actual projective
plane. The module structure is multiplication by actual regular sections.
This construction assumes no statement about cohomology or global sections. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalProjectiveTwist

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions

variable (K : Type*) [Field K]

def abPresheaf (v : ℤ) : TopCat.Presheaf Ab (plane K) where
  obj U := AddCommGrpCat.of (sectionsSubmodule K v U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun q => f.val (i.unop q),
        (isLocallyFraction K v).res i.unop f.val f.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id := by intro U; ext f q; rfl
  map_comp := by intro U V W i j; ext f q; rfl

theorem restriction_apply (v : ℤ) {U V : (plane K).Opens} (i : U ⟶ V)
    (f : (abPresheaf K v).obj (op V)) (q : U) :
    ((abPresheaf K v).map i.op f).val q = f.val (i q) := rfl

instance sectionModule (v : ℤ) (U : ((plane K).Opens)ᵒᵖ) :
    Module ((plane K).ringCatSheaf.obj.obj U) ((abPresheaf K v).obj U) :=
  inferInstanceAs (Module Γ(plane K, U.unop) (sectionsSubmodule K v U.unop))

theorem restriction_smul (v : ℤ) {U V : ((plane K).Opens)ᵒᵖ} (i : U ⟶ V)
    (s : (plane K).ringCatSheaf.obj.obj U) (f : (abPresheaf K v).obj U) :
    (abPresheaf K v).map i (s • f) =
      (plane K).ringCatSheaf.obj.map i s • (abPresheaf K v).map i f := by
  apply Subtype.ext
  funext q
  rfl

def twistPresheaf (v : ℤ) : (plane K).PresheafOfModules :=
  PresheafOfModules.ofPresheaf (abPresheaf K v)
    (fun {_ _} i s f => restriction_smul K v i s f)

def underlyingTypesIso (v : ℤ) :
    abPresheaf K v ⋙ forget Ab ≅
      subpresheafToTypes (isLocallyFraction K v).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

theorem abPresheaf_isSheaf (v : ℤ) : (abPresheaf K v).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (underlyingTypesIso K v).symm
      (subpresheafToTypes.isSheaf (isLocallyFraction K v)))

def twist (v : ℤ) : (plane K).Modules where
  val := twistPresheaf K v
  isSheaf := abPresheaf_isSheaf K v

theorem twist_sections (v : ℤ) (U : (plane K).Opens) :
    Γ(twist K v, U) = AddCommGrpCat.of (sectionsSubmodule K v U) := rfl

theorem twist_restriction_apply (v : ℤ) {U V : (plane K).Opens} (i : U ⟶ V)
    (f : Γ(twist K v, V)) (q : U) :
    ((twist K v).presheaf.map i.op f).val q = f.val (i q) := rfl

theorem twist_smul_apply (v : ℤ) (U : (plane K).Opens)
    (s : Γ(plane K, U)) (f : Γ(twist K v, U)) (q : U) :
    (s • f : Γ(twist K v, U)).val q = (s.val q).val * f.val q := rfl

end Cylinder.GlobalProjectiveTwist
end
