module

public import Cylinder.PairTorusCompatibility

/-! Actual additive restriction identities on a common open pass to
the same torus. Clearing three genuine coordinate denominators proves
the identity in the original polynomial ring first. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.GlobalTwistPairSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PairTorusAdditiveCompatibility

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistPairSections Cylinder.GlobalTwistPairFractionRepresentatives
open Cylinder.CommonTorusFractions Cylinder.PairTorusCompatibility Cylinder.ActualTorusGenericPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def genericFraction (i j : Option (Fin 2)) (a b : ℕ) (H : PlaneRing K) :
    FullLocal K (genericPoint K) :=
  Localization.mk H ⟨X i ^ a * X j ^ b, genericPoint_nonzero K _
    (mul_ne_zero (pow_ne_zero a (X_ne_zero i)) (pow_ne_zero b (X_ne_zero j)))⟩

theorem genericFraction_spec (i j : Option (Fin 2)) (a b : ℕ) (H : PlaneRing K) :
    genericFraction K i j a b H *
      algebraMap (PlaneRing K) (FullLocal K (genericPoint K)) (X i ^ a * X j ^ b) =
        algebraMap (PlaneRing K) (FullLocal K (genericPoint K)) H := by
  unfold genericFraction
  rw [Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ _ _

theorem literalFraction_sub_eq_of_generic
    (i j k l m n : Option (Fin 2)) (a b c d e f : ℕ) (H G J : PlaneRing K)
    (he : genericFraction K i j a b H - genericFraction K k l c d G =
      genericFraction K m n e f J) :
    literalFraction K i j a b H - literalFraction K k l c d G = literalFraction K m n e f J := by
  have hH := genericFraction_spec K i j a b H
  have hG := genericFraction_spec K k l c d G
  have hJ := genericFraction_spec K m n e f J
  have hp : H * (X k ^ c * X l ^ d) * (X m ^ e * X n ^ f) -
      G * (X i ^ a * X j ^ b) * (X m ^ e * X n ^ f) =
        J * (X i ^ a * X j ^ b) * (X k ^ c * X l ^ d) := by
    apply generic_algebraMap_injective K
    let g := algebraMap (PlaneRing K) (FullLocal K (genericPoint K))
    have hlocal : g H * g (X k ^ c * X l ^ d) * g (X m ^ e * X n ^ f) -
        g G * g (X i ^ a * X j ^ b) * g (X m ^ e * X n ^ f) =
          g J * g (X i ^ a * X j ^ b) * g (X k ^ c * X l ^ d) := by
      dsimp only [g]
      calc
        _ = (genericFraction K i j a b H - genericFraction K k l c d G) *
          (algebraMap (PlaneRing K) (FullLocal K (genericPoint K)) (X i ^ a * X j ^ b) *
            algebraMap (PlaneRing K) (FullLocal K (genericPoint K)) (X k ^ c * X l ^ d) *
            algebraMap (PlaneRing K) (FullLocal K (genericPoint K)) (X m ^ e * X n ^ f)) := by
              rw [← hH, ← hG]
              ring
        _ = _ := by rw [he, ← hJ]; ring
    simpa only [g, map_sub, map_mul] using hlocal
  have hunit : IsUnit (polynomialMap K (X i ^ a * X j ^ b) *
      polynomialMap K (X k ^ c * X l ^ d) * polynomialMap K (X m ^ e * X n ^ f)) := by
    rw [← denominatorUnit_value, ← denominatorUnit_value, ← denominatorUnit_value]
    exact ((denominatorUnit K i j a b).isUnit.mul (denominatorUnit K k l c d).isUnit).mul
      (denominatorUnit K m n e f).isUnit
  apply hunit.mul_right_cancel
  calc
    _ = (literalFraction K i j a b H * polynomialMap K (X i ^ a * X j ^ b)) *
        polynomialMap K (X k ^ c * X l ^ d) * polynomialMap K (X m ^ e * X n ^ f) -
      (literalFraction K k l c d G * polynomialMap K (X k ^ c * X l ^ d)) *
        polynomialMap K (X i ^ a * X j ^ b) * polynomialMap K (X m ^ e * X n ^ f) := by ring
    _ = polynomialMap K H * polynomialMap K (X k ^ c * X l ^ d) *
        polynomialMap K (X m ^ e * X n ^ f) -
      polynomialMap K G * polynomialMap K (X i ^ a * X j ^ b) *
        polynomialMap K (X m ^ e * X n ^ f) := by rw [literalFraction_clear, literalFraction_clear]
    _ = polynomialMap K J * polynomialMap K (X i ^ a * X j ^ b) *
      polynomialMap K (X k ^ c * X l ^ d) := by
        simpa only [map_sub, map_mul] using congrArg (polynomialMap K) hp
    _ = _ := by rw [← literalFraction_clear K m n e f J]; ring

theorem restriction_sub_eq
    (i j k l m n : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : genericPoint K ∈ U) (h₁ : U ≤ pairOpen K i j)
    (h₂ : U ≤ pairOpen K k l) (h₃ : U ≤ pairOpen K m n)
    (s : Γ(twist K v, pairOpen K i j)) (t : Γ(twist K v, pairOpen K k l))
    (r : Γ(twist K v, pairOpen K m n))
    (he : (twist K v).presheaf.map (homOfLE h₁).op s -
      (twist K v).presheaf.map (homOfLE h₂).op t =
        (twist K v).presheaf.map (homOfLE h₃).op r) :
    PairTorusEvaluation.torusValue K i j v s - PairTorusEvaluation.torusValue K k l v t =
      PairTorusEvaluation.torusValue K m n v r := by
  obtain ⟨ds, a, b, H, hH, hdH, hs⟩ := exists_pair_fraction K i j v s
  obtain ⟨dt, c, d, G, hG, hdG, ht⟩ := exists_pair_fraction K k l v t
  obtain ⟨dr, e, f, J, hJ, hdJ, hr⟩ := exists_pair_fraction K m n v r
  rw [torusValue_of_fraction K i j v s a b H hs,
    torusValue_of_fraction K k l v t c d G ht, torusValue_of_fraction K m n v r e f J hr]
  apply literalFraction_sub_eq_of_generic K i j k l m n a b c d e f H G J
  have hev := congrArg (fun z : Γ(twist K v, U) => z.val ⟨genericPoint K, hU⟩) he
  change s.val ⟨genericPoint K, h₁ hU⟩ - t.val ⟨genericPoint K, h₂ hU⟩ =
    r.val ⟨genericPoint K, h₃ hU⟩ at hev
  rw [hs, ht, hr] at hev
  exact hev

end Cylinder.PairTorusAdditiveCompatibility
end
