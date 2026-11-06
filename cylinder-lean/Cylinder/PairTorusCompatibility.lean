module

public import Cylinder.PairTorusEvaluation
public import Cylinder.GlobalTwistTorusCompatibility

/-! Literal pair fractions and restriction compatibility in the same
common torus. The actual-section statements derive their fraction
representatives from the previously proved chart theorems. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.GlobalTwistPairSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PairTorusCompatibility

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistPairSections Cylinder.GlobalTwistPairFractionRepresentatives
open Cylinder.CommonTorusFractions Cylinder.ChartTorusEvaluation
open Cylinder.PairTorusEvaluation Cylinder.ActualTorusGenericPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def denominatorUnit (i j : Option (Fin 2)) (a b : ℕ) : (TorusRing K)ˣ :=
  coordinateUnit K i ^ a * coordinateUnit K j ^ b

theorem denominatorUnit_value (i j : Option (Fin 2)) (a b : ℕ) :
    (denominatorUnit K i j a b : TorusRing K) = polynomialMap K (X i ^ a * X j ^ b) := by
  simp only [denominatorUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    coordinateUnit_value, map_mul, map_pow]

def literalFraction (i j : Option (Fin 2)) (a b : ℕ) (H : PlaneRing K) : TorusRing K :=
  (((denominatorUnit K i j a b)⁻¹ : (TorusRing K)ˣ) : TorusRing K) * polynomialMap K H

theorem literalFraction_clear (i j : Option (Fin 2)) (a b : ℕ) (H : PlaneRing K) :
    literalFraction K i j a b H * polynomialMap K (X i ^ a * X j ^ b) = polynomialMap K H := by
  rw [← denominatorUnit_value]
  unfold literalFraction
  calc
    _ = ((((denominatorUnit K i j a b)⁻¹ : (TorusRing K)ˣ) : TorusRing K) *
      (denominatorUnit K i j a b : TorusRing K)) * polynomialMap K H := by ring
    _ = _ := by rw [Units.inv_mul, one_mul]

theorem literalFraction_eq_of_cross (i j k l : Option (Fin 2)) (a b c d : ℕ)
    (H G : PlaneRing K) (he : H * (X k ^ c * X l ^ d) = G * (X i ^ a * X j ^ b)) :
    literalFraction K i j a b H = literalFraction K k l c d G := by
  have hunit : IsUnit
      (polynomialMap K (X i ^ a * X j ^ b) * polynomialMap K (X k ^ c * X l ^ d)) := by
    rw [← denominatorUnit_value, ← denominatorUnit_value]
    exact (denominatorUnit K i j a b).isUnit.mul (denominatorUnit K k l c d).isUnit
  apply hunit.mul_right_cancel
  calc
    _ = (literalFraction K i j a b H * polynomialMap K (X i ^ a * X j ^ b)) *
      polynomialMap K (X k ^ c * X l ^ d) := by ring
    _ = polynomialMap K H * polynomialMap K (X k ^ c * X l ^ d) := by rw [literalFraction_clear]
    _ = polynomialMap K G * polynomialMap K (X i ^ a * X j ^ b) := by
      simpa only [map_mul] using congrArg (polynomialMap K) he
    _ = (literalFraction K k l c d G * polynomialMap K (X k ^ c * X l ^ d)) *
      polynomialMap K (X i ^ a * X j ^ b) := by rw [literalFraction_clear]
    _ = _ := by ring

theorem genericPoint_mem_pairOpen (i j : Option (Fin 2)) :
    genericPoint K ∈ pairOpen K i j :=
  genericPoint_nonzero K (X i * X j) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))

theorem torusValue_of_fraction (i j : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, pairOpen K i j)) (a b : ℕ) (H : PlaneRing K)
    (hs : ∀ q : pairOpen K i j, s.val q = Localization.mk H
      ⟨X i ^ a * X j ^ b, coordinate_product_avoids K i j q a b⟩) :
    PairTorusEvaluation.torusValue K i j v s = literalFraction K i j a b H := by
  obtain ⟨c, rfl⟩ := (sectionLinearEquiv K i j v).surjective s
  obtain ⟨m, G, hG, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading K) (product_homogeneous K i j) c
  let q : pairOpen K i j := ⟨genericPoint K, genericPoint_mem_pairOpen K i j⟩
  have hcross : (X i ^ v.toNat * G) * (X i ^ a * X j ^ b) =
      H * (X i ^ (-v).toNat * (X i * X j) ^ m) := by
    apply (fraction_eq_iff_cross_mul K (X i ^ v.toNat * G) H
      ⟨X i ^ (-v).toNat * (X i * X j) ^ m, genericPoint_nonzero K _
        (mul_ne_zero (pow_ne_zero (-v).toNat (X_ne_zero i))
          (pow_ne_zero m (mul_ne_zero (X_ne_zero i) (X_ne_zero j))))⟩
      ⟨X i ^ a * X j ^ b, genericPoint_nonzero K _
        (mul_ne_zero (pow_ne_zero a (X_ne_zero i)) (pow_ne_zero b (X_ne_zero j)))⟩).mp
    exact (sectionLinearEquiv_fraction K i j v m G hG q).symm.trans (hs q)
  have hclear := torusValue_mk_clear K i j v m G hG
  have hunit : IsUnit (polynomialMap K
      (X i ^ (-v).toNat * (X i * X j) ^ m)) := by
    rw [map_mul, map_pow, map_pow]
    exact ((coordinate_unit K i).pow (-v).toNat).mul ((product_coordinate_unit K i j).pow m)
  have he : PairTorusEvaluation.torusValue K i j v
      (sectionLinearEquiv K i j v
        (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m G hG)) *
        polynomialMap K (X i ^ a * X j ^ b) = polynomialMap K H := by
    apply hunit.mul_right_cancel
    calc
      _ = (PairTorusEvaluation.torusValue K i j v
        (sectionLinearEquiv K i j v
          (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m G hG)) *
          (polynomialMap K (X i) ^ (-v).toNat * polynomialMap K (X i * X j) ^ m)) *
            polynomialMap K (X i ^ a * X j ^ b) := by
              simp only [map_mul, map_pow]
              ring
      _ = polynomialMap K (X i ^ v.toNat * G) * polynomialMap K (X i ^ a * X j ^ b) := by
        rw [hclear]
      _ = polynomialMap K H * polynomialMap K (X i ^ (-v).toNat * (X i * X j) ^ m) := by
        simpa only [map_mul] using congrArg (polynomialMap K) hcross
  apply (denominatorUnit K i j a b).isUnit.mul_right_cancel
  rw [denominatorUnit_value, literalFraction_clear]
  exact he

theorem coordinateFraction_as_pair (i j : Option (Fin 2)) (a : ℕ) (H : PlaneRing K) :
    coordinateFraction K i a H = literalFraction K i j a 0 H := by
  apply ((coordinate_unit K i).pow a).mul_right_cancel
  rw [coordinateFraction_clear]
  symm
  simpa only [pow_zero, mul_one, map_pow] using literalFraction_clear K i j a 0 H

theorem chart_restriction_value (i j : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K i)) :
    PairTorusEvaluation.torusValue K i j v
      ((twist K v).presheaf.map (homOfLE (pairOpen_le_first K i j)).op s) =
        GlobalTwistTorusCompatibility.torusValue K i v s := by
  obtain ⟨m, a, H, hH, hdH, hs⟩ :=
    GlobalTwistCoordinateFractionRepresentatives.exists_coordinate_fraction K i v s
  rw [GlobalTwistTorusCompatibility.torusValue_of_fraction K i v s m a H hH hdH hs,
    coordinateFraction_as_pair K i j a H]
  apply torusValue_of_fraction K i j v _ a 0 H
  intro q
  change s.val ⟨q.val, pairOpen_le_first K i j q.property⟩ = _
  rw [hs]
  apply congrArg (Localization.mk H)
  apply Subtype.ext
  simp only [pow_zero, mul_one]

theorem coordinateFraction_as_pair_right (i j : Option (Fin 2)) (b : ℕ) (H : PlaneRing K) :
    coordinateFraction K j b H = literalFraction K i j 0 b H := by
  apply ((coordinate_unit K j).pow b).mul_right_cancel
  rw [coordinateFraction_clear]
  symm
  simpa only [pow_zero, one_mul, map_pow] using literalFraction_clear K i j 0 b H

theorem second_chart_restriction_value (i j : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K j)) :
    PairTorusEvaluation.torusValue K i j v
      ((twist K v).presheaf.map (homOfLE (pairOpen_le_second K i j)).op s) =
        GlobalTwistTorusCompatibility.torusValue K j v s := by
  obtain ⟨m, b, H, hH, hdH, hs⟩ :=
    GlobalTwistCoordinateFractionRepresentatives.exists_coordinate_fraction K j v s
  rw [GlobalTwistTorusCompatibility.torusValue_of_fraction K j v s m b H hH hdH hs,
    coordinateFraction_as_pair_right K i j b H]
  apply torusValue_of_fraction K i j v _ 0 b H
  intro q
  change s.val ⟨q.val, pairOpen_le_second K i j q.property⟩ = _
  rw [hs]
  apply congrArg (Localization.mk H)
  apply Subtype.ext
  simp only [pow_zero, one_mul]

variable [Infinite K]

theorem literalFraction_cross_iff (i j k l : Option (Fin 2)) (a b c d r t : ℕ)
    (H G : PlaneRing K) (hH : H.IsHomogeneous r) (hG : G.IsHomogeneous t)
    (hd : r + c + d = t + a + b) :
    literalFraction K i j a b H = literalFraction K k l c d G ↔
      H * (X k ^ c * X l ^ d) = G * (X i ^ a * X j ^ b) := by
  constructor
  · intro he
    apply HomogeneousTorusInjectivity.homogeneous_injective K (r + (c + d)) _ _
      (hH.mul ((isHomogeneous_X_pow k c).mul (isHomogeneous_X_pow l d)))
      (by
        convert hG.mul ((isHomogeneous_X_pow i a).mul (isHomogeneous_X_pow j b)) using 1
        omega)
    have hmap : polynomialMap K H * polynomialMap K (X k ^ c * X l ^ d) =
        polynomialMap K G * polynomialMap K (X i ^ a * X j ^ b) := by
      calc
        _ = (literalFraction K i j a b H * polynomialMap K (X i ^ a * X j ^ b)) *
          polynomialMap K (X k ^ c * X l ^ d) := by rw [literalFraction_clear]
        _ = (literalFraction K k l c d G * polynomialMap K (X k ^ c * X l ^ d)) *
          polynomialMap K (X i ^ a * X j ^ b) := by rw [he]; ring
        _ = _ := by rw [literalFraction_clear]
    simpa only [map_mul] using hmap
  · exact literalFraction_eq_of_cross K i j k l a b c d H G

theorem torusValue_injective (i j : Option (Fin 2)) (v : ℤ) :
    Function.Injective (PairTorusEvaluation.torusValue K i j v) := by
  intro s t he
  obtain ⟨r, a, b, H, hH, hdH, hs⟩ := exists_pair_fraction K i j v s
  obtain ⟨d, c, e, G, hG, hdG, ht⟩ := exists_pair_fraction K i j v t
  rw [torusValue_of_fraction K i j v s a b H hs,
    torusValue_of_fraction K i j v t c e G ht] at he
  have hcross := (literalFraction_cross_iff K i j i j a b c e r d H G hH hG (by omega)).mp he
  apply Subtype.ext
  funext q
  exact (hs q).trans ((fraction_eq_of_cross_mul K q.val H G _ _ hcross).trans (ht q).symm)

theorem restrictions_eq_iff_torusValue (i j k l : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, pairOpen K i j)) (t : Γ(twist K v, pairOpen K k l)) :
    (twist K v).presheaf.map (homOfLE (inf_le_left :
      pairOpen K i j ⊓ pairOpen K k l ≤ pairOpen K i j)).op s =
      (twist K v).presheaf.map (homOfLE (inf_le_right :
        pairOpen K i j ⊓ pairOpen K k l ≤ pairOpen K k l)).op t ↔
      PairTorusEvaluation.torusValue K i j v s = PairTorusEvaluation.torusValue K k l v t := by
  obtain ⟨r, a, b, H, hH, hdH, hs⟩ := exists_pair_fraction K i j v s
  obtain ⟨d, c, e, G, hG, hdG, ht⟩ := exists_pair_fraction K k l v t
  rw [torusValue_of_fraction K i j v s a b H hs,
    torusValue_of_fraction K k l v t c e G ht,
    literalFraction_cross_iff K i j k l a b c e r d H G hH hG (by omega)]
  constructor
  · intro he
    let q : ↥(pairOpen K i j ⊓ pairOpen K k l) :=
      ⟨genericPoint K, genericPoint_mem_pairOpen K i j, genericPoint_mem_pairOpen K k l⟩
    have hev := congrArg (fun z : Γ(twist K v, pairOpen K i j ⊓ pairOpen K k l) => z.val q) he
    apply (fraction_eq_iff_cross_mul K H G
      ⟨X i ^ a * X j ^ b, genericPoint_nonzero K _
        (mul_ne_zero (pow_ne_zero a (X_ne_zero i)) (pow_ne_zero b (X_ne_zero j)))⟩
      ⟨X k ^ c * X l ^ e, genericPoint_nonzero K _
        (mul_ne_zero (pow_ne_zero c (X_ne_zero k)) (pow_ne_zero e (X_ne_zero l)))⟩).mp
    exact (hs ⟨q.val, q.property.1⟩).symm.trans
      (hev.trans (ht ⟨q.val, q.property.2⟩))
  · intro he
    apply Subtype.ext
    funext q
    exact (hs ⟨q.val, q.property.1⟩).trans
      ((fraction_eq_of_cross_mul K q.val H G _ _ he).trans (ht ⟨q.val, q.property.2⟩).symm)

end Cylinder.PairTorusCompatibility
end
