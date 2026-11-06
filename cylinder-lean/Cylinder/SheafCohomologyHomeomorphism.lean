module

public import Cylinder.SheafCohomologyScalarAction
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! Transport along an actual homeomorphism preserves Ext-defined sheaf
cohomology. The constant sheaf comparison is constructed from the two
global-section adjunctions, and the scalar action is the canonical action
through scalar sheaf endomorphisms. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.SheafCohomologyScalarAction
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Cylinder.SheafCohomologyHomeomorphism

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open Cylinder.SheafCohomologyScalarAction

variable {X Y : TopCat.{u}}

abbrev topology (X : TopCat.{u}) := Opens.grothendieckTopology X

/-- The genuine direct image, using the canonical site categories. -/
def pushforward (A : Type*) [Category A] (e : X ≅ Y) :
    Sheaf (topology X) A ⥤ Sheaf (topology Y) A :=
  (Opens.map e.hom).sheafPushforwardContinuous A _ _

/-- Direct image along a homeomorphism is an equivalence of actual sheaves. -/
def sheafEquivalence (A : Type*) [Category A] (e : X ≅ Y) :
    Sheaf (topology X) A ≌ Sheaf (topology Y) A where
  functor := pushforward A e
  inverse := pushforward A e.symm
  unitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso A e).unitIso.app F.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (TopCat.Presheaf.presheafEquivOfIso A e).unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso A e).counitIso.app F.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (TopCat.Presheaf.presheafEquivOfIso A e).counitIso.hom.naturality f.hom)
  functor_unitIso_comp F := by
    apply ObjectProperty.hom_ext
    exact (TopCat.Presheaf.presheafEquivOfIso A e).functor_unitIso_comp F.obj

instance pushforward_isEquivalence (A : Type*) [Category A] (e : X ≅ Y) :
    (pushforward A e).IsEquivalence :=
  (sheafEquivalence A e).isEquivalence_functor

instance pushforward_additive (e : X ≅ Y) :
    (pushforward AddCommGrpCat.{u} e).Additive where
  map_add := rfl

instance inverse_additive (e : X ≅ Y) :
    (sheafEquivalence AddCommGrpCat.{u} e).inverse.Additive :=
  pushforward_additive e.symm

instance functor_additive (e : X ≅ Y) :
    (sheafEquivalence AddCommGrpCat.{u} e).functor.Additive :=
  pushforward_additive e

instance symm_functor_additive (e : X ≅ Y) :
    (sheafEquivalence AddCommGrpCat.{u} e).symm.functor.Additive where
  map_add := rfl

instance symm_inverse_additive (e : X ≅ Y) :
    (sheafEquivalence AddCommGrpCat.{u} e).symm.inverse.Additive where
  map_add := rfl

/-- The comparison of the actual constant abelian sheaves is forced by
the global-section adjunctions; it is not an additional premise. -/
def inverseConstantIso (e : X ≅ Y) :
    (sheafEquivalence AddCommGrpCat.{u} e).inverse.obj
      ((constantSheaf (topology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (topology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  let adj : constantSheaf (topology Y) AddCommGrpCat.{u} ⋙
      (sheafEquivalence AddCommGrpCat.{u} e).inverse ⊣
      (sheafSections (topology X) AddCommGrpCat.{u}).obj (op ⊤) :=
    (constantSheafAdj (topology Y) AddCommGrpCat.{u} isTerminalTop).comp
      (sheafEquivalence AddCommGrpCat.{u} e).symm.toAdjunction
  exact (adj.leftAdjointUniq
    (constantSheafAdj (topology X) AddCommGrpCat.{u} isTerminalTop)).app _

section Precomposition

variable {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]

def extPrecomposeIso {P Q T : C} (e : P ≅ Q) (n : ℕ) :
    Ext Q T n ≃+ Ext P T n where
  toFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  left_inv x := by simp only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by simp only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := by simp

end Precomposition

/-- Homeomorphism invariance of genuine Ext-defined cohomology. -/
def cohomologyAddEquiv (e : X ≅ Y) (F : Sheaf (topology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H ((pushforward AddCommGrpCat.{u} e).obj F) n :=
  (extPrecomposeIso (T := F) (inverseConstantIso e) n).trans
    ((sheafEquivalence AddCommGrpCat.{u} e).symm.toAdjunction.extEquiv
      (X := (constantSheaf (topology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) (Y := F) (n := n))

theorem cohomologyAddEquiv_naturality (e : X ≅ Y)
    {F G : Sheaf (topology X) AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ)
    (x : Sheaf.H F n) :
    cohomologyAddEquiv e G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((pushforward AddCommGrpCat.{u} e).map f) n
        (cohomologyAddEquiv e F n x) := by
  let E := sheafEquivalence AddCommGrpCat.{u} e
  let C : Sheaf (topology Y) AddCommGrpCat.{u} :=
    (constantSheaf (topology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let a : Ext (E.inverse.obj C) F n :=
    (Ext.mk₀ (inverseConstantIso e).hom).comp x (zero_add n)
  have h : (Ext.mk₀ (inverseConstantIso e).hom).comp
      (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n) =
      a.comp (Ext.mk₀ f) (add_zero n) :=
    (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (inverseConstantIso e).hom)
      x (Ext.mk₀ f) (zero_add n)).symm
  exact (congrArg (E.symm.toAdjunction.extEquiv (X := C) (Y := G) (n := n)) h).trans
    (E.symm.toAdjunction.extEquiv_naturality_right₀
      (X := C) (Y₁ := F) (Y₂ := G) (n := n) a f)

variable {K : Type u} [CommRing K]

/-- An actual module-sheaf isomorphism induces a linear cohomology
equivalence for the canonical scalar action. -/
def cohomologyIsoLinearEquiv {F G : Sheaf (topology X) (ModuleCat.{u} K)}
    (i : F ≅ G) (n : ℕ) :
    Sheaf.H (forgetModules.obj F) n ≃ₗ[K] Sheaf.H (forgetModules.obj G) n where
  toFun x := Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.hom) n x
  invFun x := Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.inv) n x
  left_inv x := by
    change Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.inv) n
      (Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.hom) n x) = x
    rw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, i.hom_inv_id,
      CategoryTheory.Functor.map_id,
      Sheaf.H.map_id_apply]
  right_inv x := by
    change Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.hom) n
      (Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.inv) n x) = x
    rw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, i.inv_hom_id,
      CategoryTheory.Functor.map_id,
      Sheaf.H.map_id_apply]
  map_add' x y :=
    (Sheaf.H.map ((forgetModules (J := topology X) (K := K)).map i.hom) n).map_add x y
  map_smul' a x := (cohomologyMapLinear (J := topology X) (K := K)
    (F := F) (G := G) i.hom n).map_smul a x

/-- The same actual direct image on module sheaves. -/
abbrev pushforwardModules (e : X ≅ Y) := pushforward (ModuleCat.{u} K) e

/-- The same additive cohomology equivalence with its actual module
sheaf target made explicit. -/
def cohomologyPushAddEquiv (e : X ≅ Y) (F : Sheaf (topology X) (ModuleCat.{u} K)) (n : ℕ) :
    Sheaf.H ((forgetModules (J := topology X) (K := K)).obj F) n ≃+
      Sheaf.H ((forgetModules (J := topology Y) (K := K)).obj
        ((pushforwardModules (K := K) e).obj F)) n :=
  cohomologyAddEquiv e ((forgetModules (J := topology X) (K := K)).obj F) n

theorem pushforward_scalarMap (e : X ≅ Y) (F : Sheaf (topology X) (ModuleCat.{u} K))
    (a : K) :
    (pushforward AddCommGrpCat.{u} e).map (scalarMap F a) =
      scalarMap ((pushforwardModules (K := K) e).obj F) a := rfl

theorem cohomologyAddEquiv_map_smul (e : X ≅ Y)
    (F : Sheaf (topology X) (ModuleCat.{u} K)) (n : ℕ) (a : K)
    (x : Sheaf.H ((forgetModules (J := topology X) (K := K)).obj F) n) :
    cohomologyPushAddEquiv e F n (a • x) = a • cohomologyPushAddEquiv e F n x := by
  rw [cohomology_smul_def (J := topology X) (K := K) F n a x,
    cohomology_smul_def (J := topology Y) (K := K)
      ((pushforwardModules (K := K) e).obj F) n a
      (cohomologyPushAddEquiv e F n x)]
  exact (cohomologyAddEquiv_naturality e (scalarMap F a) n x).trans
    (congrArg
      (fun f : (pushforward AddCommGrpCat.{u} e).obj
          ((forgetModules (J := topology X) (K := K)).obj F) ⟶
        (pushforward AddCommGrpCat.{u} e).obj
          ((forgetModules (J := topology X) (K := K)).obj F) =>
        Sheaf.H.map f n
          (cohomologyAddEquiv e ((forgetModules (J := topology X) (K := K)).obj F) n x))
      (pushforward_scalarMap e F a))

/-- Invariance is linear for the canonical scalar action on actual Ext. -/
def cohomologyLinearEquiv (e : X ≅ Y) (F : Sheaf (topology X) (ModuleCat.{u} K)) (n : ℕ) :
    Sheaf.H (forgetModules.obj F) n ≃ₗ[K]
      Sheaf.H (forgetModules.obj ((pushforwardModules (K := K) e).obj F)) n :=
  (cohomologyPushAddEquiv e F n).toLinearEquiv (cohomologyAddEquiv_map_smul e F n)

end Cylinder.SheafCohomologyHomeomorphism

end
