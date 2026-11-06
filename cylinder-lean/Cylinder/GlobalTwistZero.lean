module

public import Cylinder.GlobalProjectiveTwist

/-! The degree-zero member of the global fraction sheaves is the actual
structure module. This identifies regular sections using the injective map
from homogeneous localization into ordinary localization. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistZero

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem regular_degree_zero (U : (plane K).Opens) (s : Γ(plane K, U)) :
    (isLocallyFraction K 0).pred (fun q : U => (s.val q).val) := by
  intro x
  rcases s.property x with ⟨V, hx, i, n, H, B, hb, he⟩
  refine ⟨V, hx, i, n, n, H.val, B.val, by omega, H.property, B.property, hb, ?_⟩
  intro q
  exact congrArg HomogeneousLocalization.val (he q)

def regularToZero (U : (plane K).Opens) :
    Γ(plane K, U) →ₗ[Γ(plane K, U)] sectionsSubmodule K 0 U where
  toFun s := ⟨fun q => (s.val q).val, regular_degree_zero K U s⟩
  map_add' s t := by
    apply Subtype.ext
    funext q
    exact HomogeneousLocalization.val_add _ _
  map_smul' s t := by
    apply Subtype.ext
    funext q
    exact HomogeneousLocalization.val_mul _ _

theorem regularToZero_apply (U : (plane K).Opens) (s : Γ(plane K, U)) (q : U) :
    (regularToZero K U s).val q = (s.val q).val := rfl

theorem regularToZero_injective (U : (plane K).Opens) :
    Function.Injective (regularToZero K U) := by
  intro s t h
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  exact congrArg (fun f : sectionsSubmodule K 0 U => f.val q) h

theorem exists_homogeneous_value (U : (plane K).Opens)
    (f : sectionsSubmodule K 0 U) (q : U) :
    ∃ z : HomogeneousLocalization.AtPrime (grading K) q.val.asHomogeneousIdeal.toIdeal,
      z.val = f.val q := by
  rcases f.property q with ⟨V, hq, i, m, n, H, B, hd, hH, hB, hb, he⟩
  have hmn : m = n := by omega
  subst m
  refine ⟨HomogeneousLocalization.mk ⟨n, ⟨H, hH⟩, ⟨B, hB⟩, hb ⟨q.val, hq⟩⟩, ?_⟩
  simpa only [HomogeneousLocalization.val_mk, Opens.apply_mk] using (he ⟨q.val, hq⟩).symm

theorem regularToZero_surjective (U : (plane K).Opens) :
    Function.Surjective (regularToZero K U) := by
  intro f
  choose z hz using exists_homogeneous_value K U f
  have hs : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction (grading K)).pred z := by
    intro x
    rcases f.property x with ⟨V, hx, i, m, n, H, B, hd, hH, hB, hb, he⟩
    have hmn : m = n := by omega
    subst m
    refine ⟨V, hx, i, n, ⟨H, hH⟩, ⟨B, hB⟩, hb, ?_⟩
    intro q
    apply HomogeneousLocalization.val_injective
    exact (hz (i q)).trans (he q)
  refine ⟨⟨z, hs⟩, ?_⟩
  apply Subtype.ext
  exact funext hz

def sectionEquiv (U : (plane K).Opens) :
    Γ(plane K, U) ≃ₗ[Γ(plane K, U)] sectionsSubmodule K 0 U :=
  LinearEquiv.ofBijective (regularToZero K U)
    ⟨regularToZero_injective K U, regularToZero_surjective K U⟩

theorem sectionEquiv_restrict {U V : (plane K).Opens} (i : U ⟶ V)
    (s : Γ(plane K, V)) :
    sectionEquiv K U ((plane K).presheaf.map i.op s) =
      (twist K 0).presheaf.map i.op (sectionEquiv K V s) := by
  apply Subtype.ext
  funext q
  rfl

def presheafIso : PresheafOfModules.unit (plane K).ringCatSheaf.obj ≅
    (twist K 0).val :=
  PresheafOfModules.isoMk (fun U => (sectionEquiv K U.unop).toModuleIso)
    (by intro U V i; rfl)

def structureIso : SheafOfModules.unit (plane K).ringCatSheaf ≅ twist K 0 where
  hom := ⟨(presheafIso K).hom⟩
  inv := ⟨(presheafIso K).inv⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    exact (presheafIso K).hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    exact (presheafIso K).inv_hom_id

end Cylinder.GlobalTwistZero
end
