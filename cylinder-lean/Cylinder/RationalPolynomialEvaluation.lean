module

public import Cylinder.RationalPointEvaluationLemmas
public import Cylinder.GlobalHomogeneousSections

/-! Evaluation of the canonical polynomial global section is the
original polynomial evaluation, in every integer degree. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPolynomialEvaluation

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.ProjectivePointInProj
open Cylinder.PlaneLaurentHomogeneous Cylinder.GlobalHomogeneousSections
open Cylinder.RationalFractionEvaluation Cylinder.RationalTwistEvaluation
open Cylinder.RationalPointEvaluationSheaf Cylinder.RationalPointEvaluationLemmas

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

theorem polynomialSection_evaluation (v : ℤ) (H : integerForms K v) (x : Fin 2 → K) :
    evaluation K v x ⊤ (by trivial) (polynomialSection K v H) = eval (normalized K x) H.val := by
  have hb : (1 : PlaneRing K) ∉ (rayPoint x).asHomogeneousIdeal :=
    Ideal.one_notMem (rayPoint x).asHomogeneousIdeal.toIdeal
  have hs : (polynomialSection K v H).val ⟨rayPoint x, trivial⟩ =
      Localization.mk H.val ⟨1, hb⟩ := (Localization.mk_one_eq_algebraMap H.val).symm
  rw [evaluation_fraction K v x ⊤ (by trivial) _ H.val 1 0 (isHomogeneous_one _ _) hb hs]
  simp only [map_one, div_one]

theorem globalEvaluation_polynomialSection {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (H : integerForms K v) (i : I) :
    globalEvaluation K v x (polynomialSection K v H) i = eval (normalized K (x i)) H.val := by
  rw [globalEvaluation_apply, polynomialSection_evaluation]

def polynomialEvaluation {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    integerForms K v →ₗ[K] (I → K) where
  toFun H i := eval (normalized K (x i)) H.val
  map_add' H G := by funext i; exact map_add _ _ _
  map_smul' a H := by
    funext i
    simp only [Submodule.coe_smul, smul_eval, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

theorem polynomialEvaluation_eq_composition {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :
    polynomialEvaluation K v x = (globalEvaluation K v x).comp (polynomialSection K v) := by
  ext H i
  exact (globalEvaluation_polynomialSection K v x H i).symm

end Cylinder.RationalPolynomialEvaluation
end
