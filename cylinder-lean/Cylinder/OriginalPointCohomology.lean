module

public import Cylinder.SheafCohomologyHomeomorphism
public import Cylinder.RationalPointCohomology
public import Cylinder.ProjectiveCoordinateIso

/-! The actual coordinate isomorphism transports the twisting sheaf and
its point evaluations to the original projective plane. The original
ideal here is a genuine kernel sheaf with skyscraper targets at the
original vanishing primes, rather than a renamed numerical defect. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.SheafCohomologyScalarAction
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Cylinder.OriginalPointCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Cylinder.ProjectiveCoordinateIso Cylinder.ProjectiveChartData
open Cylinder.ProjectivePointInProj Cylinder.GlobalTwistKSheaf
open Cylinder.RationalPointEvaluationSheaf Cylinder.RationalPointIdealSheaf
open Cylinder.SheafCohomologyHomeomorphism Cylinder.SheafCohomologyScalarAction

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local instance moduleSheafZeroMorphisms (X : TopCat.{u}) :
    HasZeroMorphisms (TopCat.Sheaf (ModuleCat.{u} K) X) :=
  RationalPointIdealSheaf.moduleSheafZeroMorphisms K X

instance pushforwardModules_additive {X Y : TopCat.{u}} (e : X ≅ Y) :
    (pushforwardModules (K := K) e).Additive where
  map_add := rfl

def coordinateHomeomorphism (c : Chart K) :
    (GlobalTwistLocalFractions.plane K).toTopCat ≅ (originalPlane K).toTopCat :=
  Scheme.forgetToTop.mapIso (coordinateIso c)

def originalPoint (c : Chart K) (P : PlanePointModel.Plane K) : originalPlane K :=
  (coordinateIso c).hom (rayPoint (c.affinePoint P))

theorem originalPoint_homogeneous_membership (c : Chart K) (P : PlanePointModel.Plane K)
    (hP : c.line P.rep ≠ 0) (H : MvPolynomial (Fin 3) K) (d : ℕ)
    (hH : H.IsHomogeneous d) :
    H ∈ (originalPoint K c P).asHomogeneousIdeal ↔ MvPolynomial.eval P.rep H = 0 := by
  exact (ProjectiveCoordinateIso.membership c _ H).trans
    (original_ray_membership c P hP H d hH)

def pointPushforwardIso {X Y : TopCat.{u}} (e : X ≅ Y) (x : X) :
    (pushforwardModules (K := K) e).obj (FinitePointSheaf.pointSheaf K X x) ≅
      FinitePointSheaf.pointSheaf K Y (e.hom x) :=
  ObjectProperty.isoMk _ (Iso.refl _)

def supportedPushforwardIso {X Y : TopCat.{u}} (e : X ≅ Y) {I : Type u} (x : I → X) :
    (pushforwardModules (K := K) e).obj (FinitePointSheaf.supportedSheaf K X x) ≅
      FinitePointSheaf.supportedSheaf K Y (fun i => e.hom (x i)) :=
  PreservesProduct.iso (pushforwardModules (K := K) e)
      (fun i => FinitePointSheaf.pointSheaf K X (x i)) ≪≫
    Pi.mapIso (fun i : I => pointPushforwardIso K e (x i))

/-- An actual module sheaf on the original Proj, transported through
the actual linear-coordinate scheme isomorphism. -/
def originalTwist (c : Chart K) (v : ℤ) :=
  (pushforwardModules (K := K) (coordinateHomeomorphism K c)).obj (twistK K v)

/-- Evaluation takes values in actual skyscraper sheaves at the original
homogeneous vanishing primes. -/
def originalEvaluation (c : Chart K) (v : ℤ) (D : Finset (PlanePointModel.Plane K)) :
    originalTwist K c v ⟶ FinitePointSheaf.supportedSheaf K (originalPlane K).toTopCat
      (fun P : D => originalPoint K c P.val) :=
  (pushforwardModules (K := K) (coordinateHomeomorphism K c)).map
      (evaluationMorphism K v (fun P : D => c.affinePoint P.val)) ≫
    (supportedPushforwardIso K (coordinateHomeomorphism K c)
      (fun P : D => rayPoint (c.affinePoint P.val))).hom

def originalIdealTwist (c : Chart K) (v : ℤ) (D : Finset (PlanePointModel.Plane K)) :=
  kernel (originalEvaluation K c v D)

/-- The kernel comparison follows from actual preservation of limits by
the homeomorphism's sheaf equivalence. -/
def originalIdealIso (c : Chart K) (v : ℤ) (D : Finset (PlanePointModel.Plane K)) :
    originalIdealTwist K c v D ≅
      (pushforwardModules (K := K) (coordinateHomeomorphism K c)).obj
        (idealTwist K v (fun P : D => c.affinePoint P.val)) :=
  kernelCompMono
      ((pushforwardModules (K := K) (coordinateHomeomorphism K c)).map
        (evaluationMorphism K v (fun P : D => c.affinePoint P.val)))
      (supportedPushforwardIso K (coordinateHomeomorphism K c)
        (fun P : D => rayPoint (c.affinePoint P.val))).hom ≪≫
    (PreservesKernel.iso (pushforwardModules (K := K) (coordinateHomeomorphism K c))
      (evaluationMorphism K v (fun P : D => c.affinePoint P.val))).symm

abbrev cohomologyOne (c : Chart K) (v : ℤ) (D : Finset (PlanePointModel.Plane K)) :=
  CategoryTheory.Sheaf.H (forgetModules.obj (originalIdealTwist K c v D)) 1

local instance originalCohomologyModule (c : Chart K) (v : ℤ)
    (D : Finset (PlanePointModel.Plane K)) : Module K (cohomologyOne K c v D) :=
  SheafCohomologyScalarAction.cohomologyModule
    (J := _root_.Opens.grothendieckTopology (originalPlane K).toTopCat) (K := K)
    (originalIdealTwist K c v D) 1

local instance chartCohomologyModule (c : Chart K) (v : ℤ)
    (D : Finset (PlanePointModel.Plane K)) :
    Module K (RationalPointCohomology.cohomologyOne K v (fun P : D => c.affinePoint P.val)) :=
  SheafCohomologyScalarAction.cohomologyModule
    (J := _root_.Opens.grothendieckTopology (GlobalTwistLocalFractions.plane K).toTopCat)
    (K := K) (idealTwist K v (fun P : D => c.affinePoint P.val)) 1

def originalChartCohomologyEquiv (c : Chart K) (v : ℤ)
    (D : Finset (PlanePointModel.Plane K)) :
    cohomologyOne K c v D ≃ₗ[K]
      RationalPointCohomology.cohomologyOne K v (fun P : D => c.affinePoint P.val) :=
  (cohomologyIsoLinearEquiv (originalIdealIso K c v D) 1).trans
    (cohomologyLinearEquiv (coordinateHomeomorphism K c)
      (idealTwist K v (fun P : D => c.affinePoint P.val)) 1).symm

variable [Infinite K]

theorem original_cohomology_finrank (c : Chart K) (v : ℤ)
    (D : Finset (PlanePointModel.Plane K))
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) :
    Module.finrank K (cohomologyOne K c v D) =
      IntegerCharacterFormulas.integerDefect (fun P : D => P.val.rep) v :=
  (originalChartCohomologyEquiv K c v D).finrank_eq.trans
    (RationalPointCohomology.chart_cohomologyOne_finrank_eq_original_defect K v c D hc)

theorem exists_original_cohomology (D : Finset (PlanePointModel.Plane K)) :
    ∃ c : Chart K, (∀ P : D, c.line P.val.rep ≠ 0) ∧
      (∀ (P : D) (H : MvPolynomial (Fin 3) K) (d : ℕ), H.IsHomogeneous d →
        (H ∈ (originalPoint K c P.val).asHomogeneousIdeal ↔
          MvPolynomial.eval P.val.rep H = 0)) ∧
      ∀ v : ℤ, Module.finrank K (cohomologyOne K c v D) =
        IntegerCharacterFormulas.integerDefect (fun P : D => P.val.rep) v := by
  obtain ⟨c, hc⟩ := RationalPointChartChoice.exists_common_chart K D
  exact ⟨c, hc, fun P H d hH => originalPoint_homogeneous_membership K c P.val (hc P) H d hH,
    fun v => original_cohomology_finrank K c v D hc⟩

end Cylinder.OriginalPointCohomology

end
