module

public import Cylinder.RationalPointEvaluationSheaf
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian

/-! The actual kernel sheaf of rational-point evaluation. Its global
sections are the kernel of the same global evaluation map. This file
does not assume or assert that evaluation is an epimorphism. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointIdealSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.ProjectivePointInProj Cylinder.RationalPointEvaluationSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

local instance moduleSheafZeroMorphisms (X : TopCat.{u}) :
    HasZeroMorphisms (TopCat.Sheaf (ModuleCat.{u} K) X) :=
  inferInstanceAs (HasZeroMorphisms (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) (ModuleCat.{u} K)))

local instance moduleSheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{u} K) X) :=
  inferInstanceAs (Preadditive (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) (ModuleCat.{u} K)))

local instance sectionsFunctor_additive (X : TopCat.{u}) (U : Opens X) :
    (FinitePointSheaf.sectionsFunctor K X U).Additive where
  map_add := rfl

def idealTwist {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    TopCat.Sheaf (ModuleCat.{u} K) (plane K).toTopCat :=
  kernel (evaluationMorphism K v x)

def sectionKernelIso {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (U : (plane K).Opens) :
    (idealTwist K v x).obj.obj (op U) ≅
      ModuleCat.of K (LinearMap.ker ((evaluationMorphism K v x).hom.app (op U)).hom) :=
  PreservesKernel.iso (FinitePointSheaf.sectionsFunctor K (plane K).toTopCat U)
    (evaluationMorphism K v x) ≪≫
      ModuleCat.kernelIsoKer ((evaluationMorphism K v x).hom.app (op U))

theorem global_evaluation_kernel {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    LinearMap.ker ((evaluationMorphism K v x).hom.app (op ⊤)).hom =
      LinearMap.ker (globalEvaluation K v x) := by
  ext s
  change ((evaluationMorphism K v x).hom.app (op ⊤)) s = 0 ↔
    FinitePointSheaf.globalSectionsLinearEquiv K (plane K).toTopCat
      (fun i => rayPoint (x i)) (((evaluationMorphism K v x).hom.app (op ⊤)) s) = 0
  exact (FinitePointSheaf.globalSectionsLinearEquiv K (plane K).toTopCat
    (fun i => rayPoint (x i))).map_eq_zero_iff.symm

def globalSectionsLinearEquiv {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    (idealTwist K v x).obj.obj (op ⊤) ≃ₗ[K] LinearMap.ker (globalEvaluation K v x) :=
  (sectionKernelIso K v x ⊤).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (global_evaluation_kernel K v x))

def evaluationSequence {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} K) (plane K).toTopCat) :=
  ShortComplex.mk (kernel.ι (evaluationMorphism K v x)) (evaluationMorphism K v x)
    (kernel.condition _)

end Cylinder.RationalPointIdealSheaf
end
