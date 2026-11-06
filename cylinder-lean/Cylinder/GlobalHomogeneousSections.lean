module

public import Cylinder.PlaneLaurentHomogeneous
public import Cylinder.GlobalTwistKSheaf
public import Cylinder.ActualTorusGenericPoint

/-! Actual homogeneous polynomials give actual global sections of the
twisting sheaf, by their original polynomial values at all Proj primes.
This map is injective; surjectivity remains a separate gluing statement. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalHomogeneousSections

open MvPolynomial AlgebraicGeometry TopCat
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.PlaneLaurentHomogeneous

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem polynomial_locally_fraction (v : ℤ) (H : integerForms K v) :
    (isLocallyFraction K v).pred
      (fun q : (⊤ : (plane K).Opens) => algebraMap (PlaneRing K) (FullLocal K q.val) H.val) := by
  by_cases hv : 0 ≤ v
  · have hH : H.val.IsHomogeneous v.toNat := by
      have hm := H.property
      change H.val ∈ (if 0 ≤ v then
        homogeneousSubmodule (Option (Fin 2)) K v.toNat else ⊥) at hm
      rw [ite_eq_left hv] at hm
      exact (mem_homogeneousSubmodule _ _).mp hm
    change (isFractionPrelocal K v).sheafify.pred _
    apply PrelocalPredicate.sheafifyOf
    refine ⟨v.toNat, 0, H.val, 1, ?_, hH, ?_, ?_, ?_⟩
    · simpa only [Int.ofNat_zero, sub_zero] using Int.toNat_of_nonneg hv
    · exact isHomogeneous_one _ _
    · intro q
      exact (Ideal.ne_top_iff_one _).mp q.val.isPrime.ne_top
    · intro q
      exact (Localization.mk_one_eq_algebraMap H.val).symm
  · have hH : H.val = 0 := by
      have hm := H.property
      change H.val ∈ (if 0 ≤ v then
        homogeneousSubmodule (Option (Fin 2)) K v.toNat else ⊥) at hm
      simpa only [ite_eq_right hv, Submodule.mem_bot] using hm
    simp only [hH, map_zero]
    change (isLocallyFraction K v).pred (0 : ∀ q : (⊤ : (plane K).Opens), FullLocal K q.val)
    exact zero_mem K v ⊤

def polynomialSection (v : ℤ) : integerForms K v →ₗ[K] sectionsSubmodule K v ⊤ where
  toFun H := ⟨fun q => algebraMap (PlaneRing K) (FullLocal K q.val) H.val,
    polynomial_locally_fraction K v H⟩
  map_add' H G := by
    apply Subtype.ext
    funext q
    exact map_add _ _ _
  map_smul' a H := by
    apply Subtype.ext
    funext q
    exact map_smul (IsScalarTower.toAlgHom K (PlaneRing K) (FullLocal K q.val)) a H.val

theorem polynomialSection_apply (v : ℤ) (H : integerForms K v) (q : (⊤ : (plane K).Opens)) :
    (polynomialSection K v H).val q = algebraMap (PlaneRing K) (FullLocal K q.val) H.val := rfl

theorem polynomialSection_injective (v : ℤ) : Function.Injective (polynomialSection K v) := by
  intro H G h
  apply Subtype.ext
  apply ActualTorusGenericPoint.generic_algebraMap_injective K
  exact congrArg (fun s : sectionsSubmodule K v ⊤ =>
    s.val ⟨ActualTorusGenericPoint.genericPoint K, trivial⟩) h

end Cylinder.GlobalHomogeneousSections
end
