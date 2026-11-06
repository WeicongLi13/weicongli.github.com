module

public import Cylinder.GlobalProjectiveTwist
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! The global homogeneous-fraction twist as an actual sheaf of
K-vector spaces. Scalars act by the original constant multiplication
in the pointwise polynomial localizations. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistKSheaf

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions
open Cylinder.CoordinateLaurentLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

theorem constant_smul_fraction (q : plane K) (a : K) (H : PlaneRing K)
    (B : q.asHomogeneousIdeal.toIdeal.primeCompl) :
    a • (Localization.mk H B : FullLocal K q) = Localization.mk (C a * H) B := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K (PlaneRing K) (FullLocal K q)]
  change algebraMap (PlaneRing K) (FullLocal K q) (C a) * Localization.mk H B = _
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]

theorem constant_smul_mem (v : ℤ) (U : (plane K).Opens) (a : K)
    (f : ∀ q : U, FullLocal K q.val) (hf : (isLocallyFraction K v).pred f) :
    (isLocallyFraction K v).pred (a • f) := by
  intro x
  rcases hf x with ⟨V, hx, i, m, n, H, B, hd, hH, hB, hb, he⟩
  refine ⟨V, hx, i, m, n, C a * H, B, hd, ?_, hB, hb, ?_⟩
  · simpa only [zero_add] using (isHomogeneous_C (Option (Fin 2)) a).mul hH
  · rintro ⟨q, hq⟩
    simp only [Subtype.forall, Opens.apply_mk] at he
    change a • f ⟨q, _⟩ = _
    exact (congrArg (fun z : FullLocal K q => a • z) (he q hq)).trans
      (constant_smul_fraction K q a H ⟨B, hb ⟨q, hq⟩⟩)

def kSections (v : ℤ) (U : (plane K).Opens) :
    Submodule K (∀ q : U, FullLocal K q.val) where
  carrier := (isLocallyFraction K v).pred
  zero_mem' := zero_mem K v U
  add_mem' := add_mem K v U _ _
  smul_mem' a f hf := constant_smul_mem K v U a f hf

instance sectionKModule (v : ℤ) (U : (plane K).Opens) :
    Module K (sectionsSubmodule K v U) :=
  inferInstanceAs (Module K (kSections K v U))

theorem constant_smul_apply (v : ℤ) (U : (plane K).Opens) (a : K)
    (f : sectionsSubmodule K v U) (q : U) :
    (a • f : sectionsSubmodule K v U).val q = a • f.val q := rfl

def kPresheaf (v : ℤ) : TopCat.Presheaf (ModuleCat.{u} K) (plane K) where
  obj U := ModuleCat.of K (sectionsSubmodule K v U.unop)
  map i := ModuleCat.ofHom
    { toFun := fun f => ⟨fun q => f.val (i.unop q),
        (isLocallyFraction K v).res i.unop f.val f.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id := by intro U; ext f q; rfl
  map_comp := by intro U V W i j; ext f q; rfl

def underlyingTypesIso (v : ℤ) :
    kPresheaf K v ⋙ forget (ModuleCat.{u} K) ≅
      subpresheafToTypes (isLocallyFraction K v).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

def underlyingAdditiveIso (v : ℤ) :
    kPresheaf K v ⋙ forget₂ (ModuleCat.{u} K) Ab ≅
      Cylinder.GlobalProjectiveTwist.abPresheaf K v :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

theorem kPresheaf_isSheaf (v : ℤ) : (kPresheaf K v).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (underlyingTypesIso K v).symm
      (subpresheafToTypes.isSheaf (isLocallyFraction K v)))

def twistK (v : ℤ) : TopCat.Sheaf (ModuleCat.{u} K) (plane K) :=
  ⟨kPresheaf K v, kPresheaf_isSheaf K v⟩

theorem twistK_restriction_apply (v : ℤ) {U V : (plane K).Opens} (i : U ⟶ V)
    (f : (twistK K v).obj.obj (op V)) (q : U) :
    ((twistK K v).obj.map i.op f).val q = f.val (i q) := rfl

end Cylinder.GlobalTwistKSheaf
end
