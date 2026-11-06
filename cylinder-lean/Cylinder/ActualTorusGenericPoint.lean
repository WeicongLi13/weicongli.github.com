module

public import Cylinder.GlobalTwistChartFrame

/-! The zero homogeneous prime is an actual point of the projective
plane and lies in all standard coordinate charts. Equality of literal
fractions there gives the original polynomial cross-multiplication. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.ActualTorusGenericPoint

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistChartFrame

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def genericPoint : plane K where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (PlaneRing K)).IsPrime
    infer_instance
  not_irrelevant_le := by
    intro h
    have hh := h (HomogeneousIdeal.mem_irrelevant_of_mem (grading K) zero_lt_one (coordinate_mem K))
    change (X none : PlaneRing K) ∈ (⊥ : Ideal (PlaneRing K)) at hh
    have hx : (X none : PlaneRing K) = 0 := Ideal.mem_bot.mp hh
    exact X_ne_zero none hx

theorem genericPoint_ideal : (genericPoint K).asHomogeneousIdeal = ⊥ := rfl

theorem genericPoint_nonzero (H : PlaneRing K) (hH : H ≠ 0) :
    H ∉ (genericPoint K).asHomogeneousIdeal := by
  change H ∉ (⊥ : Ideal (PlaneRing K))
  simpa only [Ideal.mem_bot] using hH

theorem genericPoint_mem_coordinateOpen (i : Option (Fin 2)) :
    genericPoint K ∈ coordinateOpen K i :=
  genericPoint_nonzero K (X i) (X_ne_zero i)

theorem generic_algebraMap_injective :
    Function.Injective (algebraMap (PlaneRing K) (FullLocal K (genericPoint K))) :=
  IsLocalization.injective _
    (genericPoint K).asHomogeneousIdeal.toIdeal.primeCompl_le_nonZeroDivisors

theorem fraction_eq_iff_cross_mul (H G : PlaneRing K)
    (B D : (genericPoint K).asHomogeneousIdeal.toIdeal.primeCompl) :
    (Localization.mk H B : FullLocal K (genericPoint K)) = Localization.mk G D ↔
      H * D.val = G * B.val := by
  simp only [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq']
  exact (generic_algebraMap_injective K).eq_iff

theorem coordinate_fraction_cross_eq (i j : Option (Fin 2)) (m n : ℕ) (H G : PlaneRing K)
    (h : (Localization.mk H
      ⟨X i ^ m, coordinate_power_avoids K i (coordinateOpen K i) le_rfl
        ⟨genericPoint K, genericPoint_mem_coordinateOpen K i⟩ m⟩ : FullLocal K (genericPoint K)) =
      Localization.mk G
        ⟨X j ^ n, coordinate_power_avoids K j (coordinateOpen K j) le_rfl
          ⟨genericPoint K, genericPoint_mem_coordinateOpen K j⟩ n⟩) :
    H * X j ^ n = G * X i ^ m :=
  (fraction_eq_iff_cross_mul K H G _ _).mp h

theorem fraction_eq_of_cross_mul (q : plane K) (H G : PlaneRing K)
    (B D : q.asHomogeneousIdeal.toIdeal.primeCompl) (h : H * D.val = G * B.val) :
    (Localization.mk H B : FullLocal K q) = Localization.mk G D := by
  simp only [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq']
  exact congrArg (algebraMap (PlaneRing K) (FullLocal K q)) h

end Cylinder.ActualTorusGenericPoint
end
