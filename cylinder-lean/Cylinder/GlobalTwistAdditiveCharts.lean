module

public import Cylinder.ActualAffineOpenEmbeddingLift
public import Cylinder.GlobalTwistKSheaf
public import Cylinder.GlobalTwistChartSheaf
public import Cylinder.CoordinateChartPermutation
public import Cylinder.SheafCohomologyScalarAction

/-! The actual additive sheaf underlying the global homogeneous twist
is the structure sheaf on each actual affine coordinate chart. All
isomorphisms arise from module restriction and the existing coordinate frames. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Cylinder.GlobalTwistAdditiveCharts

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite MvPolynomial
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame Cylinder.GlobalTwistChartSheaf
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateChartPermutation

attribute [local instance] MvPolynomial.gradedAlgebra

def moduleAb {X : Scheme.{u}} (M : X.Modules) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

def restrictionUnderlyingIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (ActualAffineOpenEmbeddingLift.pullback (f := f.base) f.isOpenEmbedding).obj (moduleAb M) ≅
      moduleAb (M.restrict f) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl))

def unitSpecIso (R : Type u) [CommRing R] :
    moduleAb (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≅
      ActualAffineCechOne.structureAb R :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl))

variable (K : Type u) [Field K]

def kTwistUnderlyingIso (v : ℤ) :
    SheafCohomologyScalarAction.forgetModules.obj (GlobalTwistKSheaf.twistK K v) ≅
      moduleAb (twist K v) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (GlobalTwistKSheaf.underlyingAdditiveIso K v)

def chartSpecIso (i : Index) : (coordinateOpen K i).toScheme ≅
    Spec (CommRingCat.of (coordinateRing K i)) :=
  Proj.basicOpenIsoSpec (grading K) (X i) (isHomogeneous_X K i) zero_lt_one

def chartEmbedding (i : Index) : Spec (CommRingCat.of (coordinateRing K i)) ⟶ plane K :=
  (chartSpecIso K i).inv ≫ (coordinateOpen K i).ι

instance chartEmbedding_open (i : Index) : IsOpenImmersion (chartEmbedding K i) :=
  IsOpenImmersion.comp _ _

def chartModuleIso (i : Index) (v : ℤ) :
    (twist K v).restrict (chartEmbedding K i) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (coordinateRing K i))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp (chartSpecIso K i).inv (coordinateOpen K i).ι).app
      (twist K v) ≪≫
    (Scheme.Modules.restrictFunctor (chartSpecIso K i).inv).mapIso
      (chartTrivialization K i v) ≪≫
    Scheme.Modules.restrictUnitIso (chartSpecIso K i).inv

def chartAdditiveIso (i : Index) (v : ℤ) :
    (ActualAffineOpenEmbeddingLift.pullback (f := (chartEmbedding K i).base)
      (chartEmbedding K i).isOpenEmbedding).obj
        (SheafCohomologyScalarAction.forgetModules.obj (GlobalTwistKSheaf.twistK K v)) ≅
      ActualAffineCechOne.structureAb (coordinateRing K i) :=
  (ActualAffineOpenEmbeddingLift.pullback (chartEmbedding K i).isOpenEmbedding).mapIso
      (kTwistUnderlyingIso K v) ≪≫
    restrictionUnderlyingIso (chartEmbedding K i) (twist K v) ≪≫
    (SheafOfModules.toSheaf _).mapIso (chartModuleIso K i v) ≪≫
    unitSpecIso (coordinateRing K i)

end Cylinder.GlobalTwistAdditiveCharts

end
