module

public import Cylinder.GlobalProjectiveTwistH0
public import Cylinder.RationalEvaluationDefect
public import Cylinder.SheafCohomologyLinearCokernel

/-! The genuine global-section evaluation cokernel is the original
polynomial evaluation cokernel, using the canonical polynomial section. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalGlobalEvaluationCokernel

open CategoryTheory CategoryTheory.Limits Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.RationalPointEvaluationSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] {I : Type u}

theorem globalEvaluation_range (v : ℤ) (x : I → Fin 2 → K) :
    (globalEvaluation K v x).range = RationalEvaluationDefect.evaluationSpace K v x := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨H, rfl⟩ := GlobalProjectiveTwistH0.polynomialSection_surjective K v s
    exact ⟨H, LinearMap.congr_fun
      (RationalPolynomialEvaluation.polynomialEvaluation_eq_composition K v x) H⟩
  · rintro ⟨H, rfl⟩
    exact ⟨GlobalHomogeneousSections.polynomialSection K v H,
      (LinearMap.congr_fun
        (RationalPolynomialEvaluation.polynomialEvaluation_eq_composition K v x) H).symm⟩

def pointSectionsEquiv (x : I → Fin 2 → K) :=
  FinitePointSheaf.globalSectionsLinearEquiv K (plane K).toTopCat
    (fun i => ProjectivePointInProj.rayPoint (x i))

theorem sectionRange_map (v : ℤ) (x : I → Fin 2 → K) :
    (((evaluationMorphism K v x).hom.app (op ⊤)).hom.range).map
      (pointSectionsEquiv K x).toLinearMap = RationalEvaluationDefect.evaluationSpace K v x := by
  rw [← LinearMap.range_comp]
  exact globalEvaluation_range K v x

def sectionCokernelEquiv (v : ℤ) (x : I → Fin 2 → K) :
    (((FinitePointSheaf.supportedSheaf K (plane K).toTopCat
        (fun i => ProjectivePointInProj.rayPoint (x i))).obj.obj (op ⊤)) ⧸
      ((evaluationMorphism K v x).hom.app (op ⊤)).hom.range) ≃ₗ[K]
        ((I → K) ⧸ RationalEvaluationDefect.evaluationSpace K v x) :=
  Submodule.Quotient.equiv _ _ (pointSectionsEquiv K x) (sectionRange_map K v x)

theorem sectionCokernel_finrank [Fintype I] (v : ℤ) (x : I → Fin 2 → K) :
    Module.finrank K (((FinitePointSheaf.supportedSheaf K (plane K).toTopCat
        (fun i => ProjectivePointInProj.rayPoint (x i))).obj.obj (op ⊤)) ⧸
      ((evaluationMorphism K v x).hom.app (op ⊤)).hom.range) =
        Fintype.card I - RationalEvaluationDefect.hilbert K v x := by
  rw [(sectionCokernelEquiv K v x).finrank_eq]
  exact RationalEvaluationDefect.cokernel_finrank K v x

theorem sectionCokernel_finrank_eq_relations [Fintype I] (v : ℤ) (x : I → Fin 2 → K) :
    Module.finrank K (((FinitePointSheaf.supportedSheaf K (plane K).toTopCat
        (fun i => ProjectivePointInProj.rayPoint (x i))).obj.obj (op ⊤)) ⧸
      ((evaluationMorphism K v x).hom.app (op ⊤)).hom.range) =
        Module.finrank K (IntegerEvaluationDuality.integerCoefficientRelations x v) := by
  rw [(sectionCokernelEquiv K v x).finrank_eq]
  exact RationalEvaluationDefect.cokernel_finrank_eq_original_relations K v x

end Cylinder.RationalGlobalEvaluationCokernel
end
