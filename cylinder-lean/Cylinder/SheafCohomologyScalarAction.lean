module

public import Cylinder.SheafCohomologyCokernel
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! The canonical scalar action on actual Ext-defined sheaf cohomology.
Scalars act through the genuine scalar endomorphisms of a module sheaf;
the action is independent of any presentation by a cokernel. -/

@[expose] public section
noncomputable section

universe w u

namespace Cylinder.SheafCohomologyScalarAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

set_option autoImplicit false

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {K : Type u} [CommRing K]

abbrev forgetModules : Sheaf J (ModuleCat.{u} K) ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})

instance forgetModules_additive : (forgetModules (J := J) (K := K)).Additive where
  map_add := rfl

/-- Scalar multiplication as an actual morphism of additive sheaves. -/
def scalarMap (F : Sheaf J (ModuleCat.{u} K)) (a : K) :
    (forgetModules.obj F) ⟶ (forgetModules.obj F) where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x : F.obj.obj U => a • x
          map_zero' := smul_zero a
          map_add' := smul_add a }
      naturality := by
        intro U V f
        ext x
        exact ((F.obj.map f).hom.map_smul a x).symm }

theorem scalarMap_apply (F : Sheaf J (ModuleCat.{u} K)) (a : K) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (scalarMap F a).hom.app U x = a • x := rfl

theorem scalarMap_zero (F : Sheaf J (ModuleCat.{u} K)) : scalarMap F 0 = 0 := by
  ext U x
  change (0 : K) • (show F.obj.obj U from x) = 0
  exact zero_smul K _

theorem scalarMap_one (F : Sheaf J (ModuleCat.{u} K)) : scalarMap F 1 = 𝟙 _ := by
  ext U x
  change (1 : K) • (show F.obj.obj U from x) = _
  exact one_smul K _

theorem scalarMap_add (F : Sheaf J (ModuleCat.{u} K)) (a b : K) :
    scalarMap F (a + b) = scalarMap F a + scalarMap F b := by
  ext U x
  change (a + b) • (show F.obj.obj U from x) = a • (show F.obj.obj U from x) +
    b • (show F.obj.obj U from x)
  exact add_smul a b _

theorem scalarMap_mul (F : Sheaf J (ModuleCat.{u} K)) (a b : K) :
    scalarMap F (a * b) = scalarMap F b ≫ scalarMap F a := by
  ext U x
  change (a * b) • (show F.obj.obj U from x) = a • (b • (show F.obj.obj U from x))
  exact mul_smul a b _

theorem scalarMap_naturality {F G : Sheaf J (ModuleCat.{u} K)} (f : F ⟶ G) (a : K) :
    scalarMap F a ≫ forgetModules.map f = forgetModules.map f ≫ scalarMap G a := by
  ext U x
  exact (f.hom.app U).hom.map_smul a x

variable [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

theorem cohomology_map_zero (F G : Sheaf J AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H F n) : Sheaf.H.map (0 : F ⟶ G) n x = 0 := by
  change ((Sheaf.functorH J n).map (0 : F ⟶ G)) x = 0
  rw [Functor.map_zero]
  rfl

/-- The canonical action obtained by applying the cohomology functor to
scalar endomorphisms. This does not use any section cokernel. -/
scoped instance cohomologyModule (F : Sheaf J (ModuleCat.{u} K)) (n : ℕ) :
    Module K (Sheaf.H (forgetModules.obj F) n) where
  smul a x := Sheaf.H.map (scalarMap F a) n x
  one_smul x := by
    change Sheaf.H.map (scalarMap F 1) n x = x
    rw [scalarMap_one, Sheaf.H.map_id_apply]
  mul_smul a b x := by
    change Sheaf.H.map (scalarMap F (a * b)) n x =
      Sheaf.H.map (scalarMap F a) n (Sheaf.H.map (scalarMap F b) n x)
    rw [scalarMap_mul, Sheaf.H.map_comp_apply]
  smul_zero a := (Sheaf.H.map (scalarMap F a) n).map_zero
  smul_add a x y := (Sheaf.H.map (scalarMap F a) n).map_add x y
  zero_smul x := by
    change Sheaf.H.map (scalarMap F 0) n x = 0
    rw [scalarMap_zero]
    exact cohomology_map_zero _ _ n x
  add_smul a b x := by
    change Sheaf.H.map (scalarMap F (a + b)) n x =
      Sheaf.H.map (scalarMap F a) n x + Sheaf.H.map (scalarMap F b) n x
    rw [scalarMap_add, Sheaf.H.map_add_apply]

open scoped Cylinder.SheafCohomologyScalarAction

theorem cohomology_smul_def (F : Sheaf J (ModuleCat.{u} K)) (n : ℕ)
    (a : K) (x : Sheaf.H (forgetModules.obj F) n) :
    a • x = Sheaf.H.map (scalarMap F a) n x := rfl

/-- Cohomology maps induced by actual module-sheaf morphisms are linear
for the scalar action just constructed. -/
def cohomologyMapLinear {F G : Sheaf J (ModuleCat.{u} K)} (f : F ⟶ G) (n : ℕ) :
    Sheaf.H (forgetModules.obj F) n →ₗ[K] Sheaf.H (forgetModules.obj G) n where
  toAddHom := Sheaf.H.map (forgetModules.map f) n
  map_smul' a x := by
    change Sheaf.H.map (forgetModules.map f) n (Sheaf.H.map (scalarMap F a) n x) =
      Sheaf.H.map (scalarMap G a) n (Sheaf.H.map (forgetModules.map f) n x)
    rw [← Sheaf.H.map_comp_apply, scalarMap_naturality, Sheaf.H.map_comp_apply]

/-- The genuine degree-zero cohomology/section equivalence is linear. -/
def cohomologyZeroLinearEquiv (F : Sheaf J (ModuleCat.{u} K))
    {T : C} (hT : IsTerminal T) :
    Sheaf.H (forgetModules.obj F) 0 ≃ₗ[K] F.obj.obj (op T) where
  toAddEquiv := Sheaf.H.equiv₀ (forgetModules.obj F) hT
  map_smul' a x := by
    exact (Sheaf.H.equiv₀_naturality (f := scalarMap F a) hT x).symm

end Cylinder.SheafCohomologyScalarAction

end
