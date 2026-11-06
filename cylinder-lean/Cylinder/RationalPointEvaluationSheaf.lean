module

public import Cylinder.RationalTwistEvaluation

/-! A genuine morphism from the projective twisting sheaf to the
product of skyscraper sheaves at the original rational points. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointEvaluationSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.ProjectivePointInProj Cylinder.RationalTwistEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

def evaluationCocone (v : ℤ) (x : Fin 2 → K) :
    Cocone ((OpenNhds.inclusion (X := (plane K).toTopCat) (rayPoint x)).op ⋙
      (twistK K v).obj) where
  pt := ModuleCat.of K K
  ι :=
    { app := fun U => ModuleCat.ofHom (evaluation K v x U.unop.val U.unop.property)
      naturality := by
        intro U V i
        ext s
        rfl }

def stalkEvaluation (v : ℤ) (x : Fin 2 → K) :
    TopCat.Presheaf.stalk (X := (plane K).toTopCat) (twistK K v).obj (rayPoint x) ⟶
      ModuleCat.of K K :=
  colimit.desc _ (evaluationCocone K v x)

theorem germ_stalkEvaluation (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) :
    TopCat.Presheaf.germ (X := (plane K).toTopCat) (twistK K v).obj U (rayPoint x) hx ≫
      stalkEvaluation K v x = (evaluationCocone K v x).ι.app (op ⟨U, hx⟩) :=
  by apply colimit.ι_desc

def pointEvaluation (v : ℤ) (x : Fin 2 → K) :
    twistK K v ⟶ FinitePointSheaf.pointSheaf K (plane K).toTopCat (rayPoint x) := by
  refine ⟨?_⟩
  change (twistK K v).obj ⟶
    skyscraperPresheaf (X := (plane K).toTopCat) (rayPoint x) (ModuleCat.of K K)
  exact StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
    (𝓕 := (twistK K v).obj) (rayPoint x) (stalkEvaluation K v x)

def evaluationMorphism {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    twistK K v ⟶ FinitePointSheaf.supportedSheaf K (plane K).toTopCat (fun i => rayPoint (x i)) :=
  Pi.lift (fun i => pointEvaluation K v (x i))

theorem evaluationMorphism_projection {I : Type u} (v : ℤ) (x : I → Fin 2 → K) (i : I) :
    evaluationMorphism K v x ≫ Pi.π _ i = pointEvaluation K v (x i) :=
  Pi.lift_comp_π _ i

def globalEvaluation {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    sectionsSubmodule K v ⊤ →ₗ[K] (I → K) :=
  (FinitePointSheaf.globalSectionsLinearEquiv K (plane K).toTopCat
    (fun i => rayPoint (x i))).toLinearMap.comp
      ((evaluationMorphism K v x).hom.app (op ⊤)).hom

end Cylinder.RationalPointEvaluationSheaf
end
