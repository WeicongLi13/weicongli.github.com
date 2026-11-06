module

public import Cylinder.RationalPointIdealSheaf
public import Cylinder.RationalPointEvaluationLemmas
public import Cylinder.FinitePointFlasque
public import Cylinder.GlobalTwistZero

/-! Sections of the actual evaluation kernel are precisely the local
homogeneous-fraction sections vanishing at the prescribed rational points.
They are closed under the actual regular-function action. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointIdealSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf Cylinder.ProjectivePointInProj
open Cylinder.RationalTwistEvaluation Cylinder.RationalPointEvaluationSheaf
open Cylinder.RationalPointEvaluationLemmas Cylinder.RationalPointIdealSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

theorem component_evaluation {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (U : (plane K).Opens) (s : sectionsSubmodule K v U) (i : I) (hi : rayPoint (x i) ∈ U) :
    (pointSectionIso K (x i) U hi).hom
      ((Pi.π (fun j => FinitePointSheaf.pointSheaf K (plane K).toTopCat (rayPoint (x j))) i).hom.app
        (op U) ((evaluationMorphism K v x).hom.app (op U) s)) =
      evaluation K v (x i) U hi s := by
  have h := congrArg (fun f => f.hom.app (op U)) (evaluationMorphism_projection K v x i)
  have hs := ConcreteCategory.congr_hom h s
  change (pointSectionIso K (x i) U hi).hom
    (((evaluationMorphism K v x ≫ Pi.π _ i).hom.app (op U)) s) = _
  rw [hs]
  exact pointEvaluation_onOpen_apply K v (x i) U hi s

def vanishingSections {I : Type u} (v : ℤ) (x : I → Fin 2 → K) (U : (plane K).Opens) :
    Submodule K (sectionsSubmodule K v U) where
  carrier s := ∀ i, ∀ hi : rayPoint (x i) ∈ U, evaluation K v (x i) U hi s = 0
  zero_mem' i hi := map_zero _
  add_mem' hf hg i hi := by rw [map_add, hf i hi, hg i hi, add_zero]
  smul_mem' a s hs i hi := by rw [map_smul, hs i hi, smul_zero]

theorem kernel_eq_vanishingSections {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (U : (plane K).Opens) :
    LinearMap.ker ((evaluationMorphism K v x).hom.app (op U)).hom = vanishingSections K v x U := by
  ext s
  constructor
  · intro hs
    change (evaluationMorphism K v x).hom.app (op U) s = 0 at hs
    intro i hi
    have hz := congrArg (fun t => (pointSectionIso K (x i) U hi).hom
      ((Pi.π (fun j => FinitePointSheaf.pointSheaf K (plane K).toTopCat (rayPoint (x j))) i).hom.app
        (op U) t)) hs
    exact (component_evaluation K v x U s i hi).symm.trans (by simpa only [map_zero] using hz)
  · intro hs
    change ∀ i, ∀ hi : rayPoint (x i) ∈ U, evaluation K v (x i) U hi s = 0 at hs
    change (evaluationMorphism K v x).hom.app (op U) s = 0
    apply (Cylinder.FinitePointFlasque.rawSectionsLinearEquiv K (plane K).toTopCat
      (fun i => rayPoint (x i)) U).injective
    funext i
    simp only [Cylinder.FinitePointFlasque.rawSectionsLinearEquiv_apply, map_zero]
    by_cases hi : rayPoint (x i) ∈ U
    · have he := (component_evaluation K v x U s i hi).trans (hs i hi)
      calc
        _ = (pointSectionIso K (x i) U hi).inv
            ((pointSectionIso K (x i) U hi).hom _) := (ModuleCat.inv_hom_apply _ _).symm
        _ = (pointSectionIso K (x i) U hi).inv 0 := congrArg _ he
        _ = 0 := map_zero _
    · letI : Subsingleton ((FinitePointSheaf.pointSheaf K (plane K).toTopCat
          (rayPoint (x i))).obj.obj (op U)) := ModuleCat.subsingleton_of_isZero
        (isTerminalSkyscraperSheafObjObjOfNotMem (A := ModuleCat.of K K) hi).isZero
      exact Subsingleton.elim _ _

def sectionsLinearEquiv {I : Type u} (v : ℤ) (x : I → Fin 2 → K) (U : (plane K).Opens) :
    (idealTwist K v x).obj.obj (op U) ≃ₗ[K] vanishingSections K v x U :=
  (sectionKernelIso K v x U).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (kernel_eq_vanishingSections K v x U))

theorem regular_smul_evaluation (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) (a : Γ(plane K, U)) (f : sectionsSubmodule K v U) :
    evaluation K v x U hx (a • f) =
      evaluation K 0 x U hx (GlobalTwistZero.regularToZero K U a) * evaluation K v x U hx f := by
  let A := sectionToRange K 0 x U hx (GlobalTwistZero.regularToZero K U a)
  let F := sectionToRange K v x U hx f
  have he : sectionToRange K v x U hx (a • f) = A * F := by apply Subtype.ext; rfl
  change RationalFractionEvaluation.rangeEvaluation K x (sectionToRange K v x U hx (a • f)) =
    RationalFractionEvaluation.rangeEvaluation K x A * RationalFractionEvaluation.rangeEvaluation K x F
  rw [he, map_mul]

def vanishingRegularSubmodule {I : Type u} (v : ℤ) (x : I → Fin 2 → K) (U : (plane K).Opens) :
    Submodule Γ(plane K, U) (sectionsSubmodule K v U) where
  carrier := (vanishingSections K v x U).carrier
  zero_mem' := (vanishingSections K v x U).zero_mem
  add_mem' hf hg := (vanishingSections K v x U).add_mem hf hg
  smul_mem' a f hf i hi := by rw [regular_smul_evaluation, hf i hi, mul_zero]

end Cylinder.RationalPointIdealSections
end
