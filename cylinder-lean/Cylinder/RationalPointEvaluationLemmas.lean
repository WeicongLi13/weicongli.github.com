module

public import Cylinder.RationalPointEvaluationSheaf
public import Cylinder.FinitePointSheafProjections

/-! The actual sheaf morphism has exactly the original pointwise
evaluation as its component on sections. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointEvaluationLemmas

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.ProjectivePointInProj Cylinder.RationalTwistEvaluation
open Cylinder.RationalPointEvaluationSheaf Cylinder.FinitePointSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

def pointSectionIso (x : Fin 2 → K) (U : (plane K).Opens) (hx : rayPoint x ∈ U) :
    (pointSheaf K (plane K).toTopCat (rayPoint x)).obj.obj (op U) ≅ ModuleCat.of K K :=
  eqToIso (by change (if rayPoint x ∈ U then ModuleCat.of K K else terminal (ModuleCat K)) = _
              simp only [ite_eq_left hx])

theorem pointEvaluation_onOpen (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) :
    (pointEvaluation K v x).hom.app (op U) ≫ (pointSectionIso K x U hx).hom =
      ModuleCat.ofHom (evaluation K v x U hx) := by
  dsimp only [pointEvaluation, pointSectionIso, id_eq]
  rw [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, dite_eq_left hx]
  simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact germ_stalkEvaluation K v x U hx

theorem pointEvaluation_onOpen_apply (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) (s : sectionsSubmodule K v U) :
    (pointSectionIso K x U hx).hom ((pointEvaluation K v x).hom.app (op U) s) =
      evaluation K v x U hx s :=
  ConcreteCategory.congr_hom (pointEvaluation_onOpen K v x U hx) s

theorem globalEvaluation_apply {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (s : sectionsSubmodule K v ⊤) (i : I) :
    globalEvaluation K v x s i = evaluation K v (x i) ⊤ (by trivial) s := by
  change globalSectionsLinearEquiv K (plane K).toTopCat (fun j => rayPoint (x j))
    ((evaluationMorphism K v x).hom.app (op ⊤) s) i = _
  rw [FinitePointSheafProjections.globalSectionsLinearEquiv_apply]
  have h := congrArg (fun f => f.hom.app (op (⊤ : (plane K).Opens)))
    (evaluationMorphism_projection K v x i)
  have hs := ConcreteCategory.congr_hom h s
  change (pointGlobalSectionsIso K (plane K).toTopCat (rayPoint (x i))).hom
    (((evaluationMorphism K v x ≫ Pi.π _ i).hom.app (op ⊤)) s) = _
  rw [hs]
  exact pointEvaluation_onOpen_apply K v (x i) ⊤ (by trivial) s

end Cylinder.RationalPointEvaluationLemmas
end
