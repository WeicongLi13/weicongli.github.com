module

public import Cylinder.GlobalTwistCoordinateFractionRepresentatives
public import Cylinder.ActualTorusGenericPoint
public import Cylinder.HomogeneousTorusInjectivity
public import Cylinder.TorusTwistFractionShift
public import Cylinder.GlobalTwistKSheaf

/-! Restrictions of actual twisting-sheaf sections agree exactly when
their literal values in the common affine torus agree. The converse uses
homogeneity; no map from an entire projective local ring to the torus is used. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistTorusCompatibility

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame Cylinder.GlobalTwistCoordinateSections
open Cylinder.CommonTorusFractions Cylinder.ChartTorusEvaluation
open Cylinder.GlobalTwistCoordinateFractionRepresentatives

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def torusValue (i : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K i)) : TorusRing K :=
  (((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
    coordinateRingMap K i ((sectionLinearEquiv K i v).symm s)

theorem torusValue_coordinate_fraction (i : Option (Fin 2)) (v : ℤ) (m n : ℕ)
    (H : PlaneRing K) (hH : H ∈ grading K (m • (1 : ℕ))) (hd : (m : ℤ) - n = v) :
    torusValue K i v (sectionLinearEquiv K i v
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH)) =
      coordinateFraction K i n H := by
  unfold torusValue
  rw [LinearEquiv.symm_apply_apply]
  change (((coordinateUnit K i) ^ v : (TorusRing K)ˣ) : TorusRing K) *
    coordinateMap K i
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  exact TorusTwistFractionShift.shifted_fraction K i v m n H hd

theorem torusValue_of_fraction (i : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K i)) (m n : ℕ) (H : PlaneRing K)
    (hH : H.IsHomogeneous m) (hd : (m : ℤ) - n = v)
    (hs : ∀ q : coordinateOpen K i, s.val q = Localization.mk H
      ⟨X i ^ n, coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩) :
    torusValue K i v s = coordinateFraction K i n H := by
  have hm : H ∈ grading K (m • (1 : ℕ)) := by simpa using hH
  have he : s = sectionLinearEquiv K i v
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hm) := by
    apply Subtype.ext
    funext q
    exact (hs q).trans (sectionLinearEquiv_fraction K i v m n H hm hd q).symm
  rw [he]
  exact torusValue_coordinate_fraction K i v m n H hm hd

variable [Infinite K]

theorem restriction_eq_iff_torusValue (i j : Option (Fin 2)) (v : ℤ)
    (s : Γ(twist K v, coordinateOpen K i)) (t : Γ(twist K v, coordinateOpen K j)) :
    (twist K v).presheaf.map (homOfLE (inf_le_left :
      coordinateOpen K i ⊓ coordinateOpen K j ≤ coordinateOpen K i)).op s =
      (twist K v).presheaf.map (homOfLE (inf_le_right :
        coordinateOpen K i ⊓ coordinateOpen K j ≤ coordinateOpen K j)).op t ↔
      torusValue K i v s = torusValue K j v t := by
  obtain ⟨a, m, H, hH, hdH, hs⟩ := exists_coordinate_fraction K i v s
  obtain ⟨b, n, G, hG, hdG, ht⟩ := exists_coordinate_fraction K j v t
  rw [torusValue_of_fraction K i v s a m H hH hdH hs,
    torusValue_of_fraction K j v t b n G hG hdG ht]
  rw [HomogeneousTorusInjectivity.coordinateFraction_cross_iff K i j m n a b H G hH hG
    (by omega)]
  constructor
  · intro he
    let q : ↥(coordinateOpen K i ⊓ coordinateOpen K j) :=
      ⟨ActualTorusGenericPoint.genericPoint K,
        ActualTorusGenericPoint.genericPoint_mem_coordinateOpen K i,
        ActualTorusGenericPoint.genericPoint_mem_coordinateOpen K j⟩
    have hev := congrArg (fun z : Γ(twist K v, coordinateOpen K i ⊓ coordinateOpen K j) =>
      z.val q) he
    apply ActualTorusGenericPoint.coordinate_fraction_cross_eq K i j m n H G
    exact (hs ⟨q.val, q.property.1⟩).symm.trans
      (hev.trans (ht ⟨q.val, q.property.2⟩))
  · intro he
    apply Subtype.ext
    funext q
    exact (hs ⟨q.val, q.property.1⟩).trans
      ((ActualTorusGenericPoint.fraction_eq_of_cross_mul K q.val H G _ _ he).trans
        (ht ⟨q.val, q.property.2⟩).symm)

theorem compatible_iff_torusValue
    (v : ℤ) (s : ∀ i : Option (Fin 2), Γ(twist K v, coordinateOpen K i)) :
    TopCat.Presheaf.IsCompatible (GlobalTwistKSheaf.twistK K v).obj (coordinateOpen K) s ↔
      ∀ i j, torusValue K i v (s i) = torusValue K j v (s j) := by
  constructor
  · intro hs i j
    exact (restriction_eq_iff_torusValue K i j v (s i) (s j)).mp (hs i j)
  · intro hs i j
    exact (restriction_eq_iff_torusValue K i j v (s i) (s j)).mpr (hs i j)

end Cylinder.GlobalTwistTorusCompatibility
end
