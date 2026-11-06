module

public import Cylinder.GlobalTwistZero
public import Cylinder.GlobalTwistMultiplication

/-! Powers of an actual homogeneous coordinate give local frames for the
global twisting sheaves. All values and inverses live in the original
polynomial localizations at actual projective primes. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistChartFrame

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev coordinateOpen (i : Option (Fin 2)) : (plane K).Opens :=
  Proj.basicOpen (grading K) (X i)

theorem coordinate_power_avoids (i : Option (Fin 2)) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (q : U) (n : ℕ) :
    X i ^ n ∉ q.val.asHomogeneousIdeal := by
  intro h
  exact hU q.property (q.val.isPrime.mem_of_pow_mem n h)

def frame (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) : sectionsSubmodule K v U := by
  refine ⟨fun q => Localization.mk (X i ^ v.toNat)
    ⟨X i ^ (-v).toNat, coordinate_power_avoids K i U hU q (-v).toNat⟩, ?_⟩
  change (isFractionPrelocal K v).sheafify.pred
    (fun q : U => (Localization.mk (X i ^ v.toNat)
      ⟨X i ^ (-v).toNat, coordinate_power_avoids K i U hU q (-v).toNat⟩ : FullLocal K q.val))
  apply PrelocalPredicate.sheafifyOf
  exact ⟨v.toNat, (-v).toNat, X i ^ v.toNat, X i ^ (-v).toNat,
    by omega, isHomogeneous_X_pow i v.toNat, isHomogeneous_X_pow i (-v).toNat,
    fun q => coordinate_power_avoids K i U hU q (-v).toNat, fun _ => rfl⟩

theorem frame_apply (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (q : U) :
    (frame K i v U hU).val q = Localization.mk (X i ^ v.toNat)
      ⟨X i ^ (-v).toNat, coordinate_power_avoids K i U hU q (-v).toNat⟩ := rfl

theorem frame_mul_inverse (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (q : U) :
    (frame K i v U hU).val q * (frame K i (-v) U hU).val q = 1 := by
  simp only [frame_apply, neg_neg, Localization.mk_mul]
  have heq :
      (⟨X i ^ (-v).toNat, coordinate_power_avoids K i U hU q (-v).toNat⟩ *
        ⟨X i ^ v.toNat, coordinate_power_avoids K i U hU q v.toNat⟩ :
          q.val.asHomogeneousIdeal.toIdeal.primeCompl) =
      ⟨X i ^ v.toNat * X i ^ (-v).toNat,
        q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
          (coordinate_power_avoids K i U hU q v.toNat)
          (coordinate_power_avoids K i U hU q (-v).toNat)⟩ :=
    Subtype.ext (mul_comm _ _)
  rw [heq, Localization.mk_eq_mk'_apply, IsLocalization.mk'_self]

def frameEquiv (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) :
    sectionsSubmodule K 0 U ≃ₗ[Γ(plane K, U)] sectionsSubmodule K v U where
  toFun f := ⟨(frame K i v U hU).val * f.val, by
    change (isLocallyFraction K v).pred _
    simpa only [add_zero] using GlobalTwistMultiplication.mul_mem K v 0 U
      (frame K i v U hU).val f.val (frame K i v U hU).property f.property⟩
  invFun f := ⟨(frame K i (-v) U hU).val * f.val, by
    change (isLocallyFraction K 0).pred _
    simpa only [neg_add_cancel] using GlobalTwistMultiplication.mul_mem K (-v) v U
      (frame K i (-v) U hU).val f.val (frame K i (-v) U hU).property f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext q
    change (frame K i (-v) U hU).val q * ((frame K i v U hU).val q * f.val q) = f.val q
    rw [← mul_assoc, mul_comm (frame K i (-v) U hU |>.val q),
      frame_mul_inverse, one_mul]
  right_inv f := by
    apply Subtype.ext
    funext q
    change (frame K i v U hU).val q * ((frame K i (-v) U hU).val q * f.val q) = f.val q
    rw [← mul_assoc, frame_mul_inverse, one_mul]
  map_add' f g := by
    apply Subtype.ext
    funext q
    change (frame K i v U hU).val q * (f.val q + g.val q) =
      (frame K i v U hU).val q * f.val q + (frame K i v U hU).val q * g.val q
    exact mul_add _ _ _
  map_smul' s f := by
    apply Subtype.ext
    funext q
    change (frame K i v U hU).val q * ((s.val q).val * f.val q) =
      (s.val q).val * ((frame K i v U hU).val q * f.val q)
    exact mul_left_comm _ _ _

def chartSectionEquiv (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) :
    Γ(plane K, U) ≃ₗ[Γ(plane K, U)] Γ(twist K v, U) :=
  (GlobalTwistZero.sectionEquiv K U).trans (frameEquiv K i v U hU)

theorem chartSectionEquiv_apply (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (s : Γ(plane K, U)) (q : U) :
    (chartSectionEquiv K i v U hU s).val q =
      (frame K i v U hU).val q * (s.val q).val := rfl

theorem chartSectionEquiv_restrict (i : Option (Fin 2)) (v : ℤ)
    {U V : (plane K).Opens} (j : U ⟶ V) (hV : V ≤ coordinateOpen K i)
    (s : Γ(plane K, V)) :
    chartSectionEquiv K i v U ((leOfHom j).trans hV) ((plane K).presheaf.map j.op s) =
      (twist K v).presheaf.map j.op (chartSectionEquiv K i v V hV s) := by
  apply Subtype.ext
  funext q
  rfl

end Cylinder.GlobalTwistChartFrame
end
