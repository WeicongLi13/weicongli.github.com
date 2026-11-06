module

public import Cylinder.GlobalTwistCoordinateSections

/-! Actual sections on pairwise standard-chart intersections come
from the actual degree-zero localization at X_i X_j, multiplied by
the same X_i-frame. Literal product-denominator fractions and actual
restriction are preserved. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistPairSections

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev pairOpen (i j : Option (Fin 2)) : (plane K).Opens :=
  Proj.basicOpen (grading K) (X i * X j)

theorem pairOpen_eq (i j : Option (Fin 2)) :
    pairOpen K i j = coordinateOpen K i ⊓ coordinateOpen K j :=
  ProjectiveSpectrum.basicOpen_mul (grading K) (X i) (X j)

theorem pairOpen_le_first (i j : Option (Fin 2)) : pairOpen K i j ≤ coordinateOpen K i :=
  ProjectiveSpectrum.basicOpen_mul_le_left (grading K) (X i) (X j)

abbrev pairRing (i j : Option (Fin 2)) :=
  HomogeneousLocalization.Away (grading K) (X i * X j : PlaneRing K)

theorem product_homogeneous (i j : Option (Fin 2)) :
    (X i * X j : PlaneRing K) ∈ grading K 2 :=
  (isHomogeneous_X K i).mul (isHomogeneous_X K j)

scoped instance pairKModule (i j : Option (Fin 2)) : Module K (pairRing K i j) :=
  Function.Injective.module K
    (algebraMap (pairRing K i j) (Localization.Away (X i * X j : PlaneRing K))).toAddMonoidHom
    (HomogeneousLocalization.val_injective (Submonoid.powers (X i * X j : PlaneRing K)))
    (fun a z => HomogeneousLocalization.val_smul (Submonoid.powers (X i * X j : PlaneRing K)) a z)

open scoped Cylinder.GlobalTwistPairSections

theorem product_power_avoids (i j : Option (Fin 2)) (q : pairOpen K i j) (m : ℕ) :
    (X i * X j : PlaneRing K) ^ m ∉ q.val.asHomogeneousIdeal :=
  fun h => q.property (q.val.isPrime.mem_of_pow_mem m h)

def constantFraction (i j : Option (Fin 2)) (a : K) : pairRing K i j :=
  HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) 0 (C a) (by simp)

theorem constantFraction_val (i j : Option (Fin 2)) (a : K) :
    (constantFraction K i j a).val =
      algebraMap K (Localization.Away (X i * X j : PlaneRing K)) a := by
  rw [constantFraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  change IsLocalization.mk' (Localization.Away (X i * X j : PlaneRing K)) (C a) 1 = _
  rw [IsLocalization.mk'_one]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K)
    (Localization.Away (X i * X j : PlaneRing K)) a).symm

theorem smul_eq_constant_mul (i j : Option (Fin 2)) (a : K) (c : pairRing K i j) :
    a • c = constantFraction K i j a * c := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, constantFraction_val]
  exact Algebra.smul_def _ _

theorem away_fraction_value (i j : Option (Fin 2)) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (2 : ℕ))) (q : pairOpen K i j) :
    ((Proj.awayToSection (grading K) (X i * X j)
      (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH)).val q).val =
      Localization.mk H ⟨(X i * X j) ^ m, product_power_avoids K i j q m⟩ := by
  refine (ProjectiveSpectrum.Proj.awayToSection_apply (grading K) (X i * X j)
    (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH) q).trans ?_
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply, IsLocalization.map_mk']
  rw [Localization.mk_eq_mk'_apply]
  exact congrArg (fun b : q.val.asHomogeneousIdeal.toIdeal.primeCompl =>
    IsLocalization.mk' (FullLocal K q.val) H b) (Subtype.ext rfl)

def pairSection (i j : Option (Fin 2)) (v : ℤ) (c : pairRing K i j) :
    Γ(twist K v, pairOpen K i j) :=
  chartSectionEquiv K i v (pairOpen K i j) (pairOpen_le_first K i j)
    (Proj.awayToSection (grading K) (X i * X j) c)

def sectionEquiv (i j : Option (Fin 2)) (v : ℤ) :
    pairRing K i j ≃ Γ(twist K v, pairOpen K i j) :=
  (Iso.commRingCatIsoToRingEquiv
    (Proj.basicOpenIsoAway (grading K) (X i * X j) (product_homogeneous K i j) (by decide))).toEquiv.trans
      (chartSectionEquiv K i v (pairOpen K i j) (pairOpen_le_first K i j)).toEquiv

theorem pairSection_add (i j : Option (Fin 2)) (v : ℤ) (c d : pairRing K i j) :
    pairSection K i j v (c + d) = pairSection K i j v c + pairSection K i j v d := by
  unfold pairSection
  rw [map_add, map_add]

theorem away_constant_value (i j : Option (Fin 2)) (a : K) (q : pairOpen K i j) :
    ((Proj.awayToSection (grading K) (X i * X j) (constantFraction K i j a)).val q).val =
      algebraMap K (FullLocal K q.val) a := by
  have h := away_fraction_value K i j 0 (C a) (by simp) q
  refine h.trans ?_
  change Localization.mk (C a) (1 : q.val.asHomogeneousIdeal.toIdeal.primeCompl) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K) (FullLocal K q.val) a).symm

theorem pairSection_smul (i j : Option (Fin 2)) (v : ℤ) (a : K) (c : pairRing K i j) :
    pairSection K i j v (a • c) = a • pairSection K i j v c := by
  apply Subtype.ext
  funext q
  change (frame K i v (pairOpen K i j) (pairOpen_le_first K i j)).val q *
      ((Proj.awayToSection (grading K) (X i * X j) (a • c)).val q).val =
    a • ((frame K i v (pairOpen K i j) (pairOpen_le_first K i j)).val q *
      ((Proj.awayToSection (grading K) (X i * X j) c).val q).val)
  rw [smul_eq_constant_mul, map_mul, AlgebraicGeometry.Proj.mul_apply,
    HomogeneousLocalization.val_mul, away_constant_value, Algebra.smul_def]
  exact mul_left_comm _ _ _

def sectionLinearEquiv (i j : Option (Fin 2)) (v : ℤ) :
    pairRing K i j ≃ₗ[K] Γ(twist K v, pairOpen K i j) where
  __ := sectionEquiv K i j v
  map_add' := pairSection_add K i j v
  map_smul' := pairSection_smul K i j v

theorem sectionLinearEquiv_fraction (i j : Option (Fin 2)) (v : ℤ) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (2 : ℕ))) (q : pairOpen K i j) :
    (sectionLinearEquiv K i j v
      (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH)).val q =
      Localization.mk (X i ^ v.toNat * H)
        ⟨X i ^ (-v).toNat * (X i * X j) ^ m,
          q.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
            (coordinate_power_avoids K i (pairOpen K i j) (pairOpen_le_first K i j) q (-v).toNat)
            (product_power_avoids K i j q m)⟩ := by
  change (frame K i v (pairOpen K i j) (pairOpen_le_first K i j)).val q *
    ((Proj.awayToSection (grading K) (X i * X j)
      (HomogeneousLocalization.Away.mk (grading K) (product_homogeneous K i j) m H hH)).val q).val = _
  rw [frame_apply, away_fraction_value, Localization.mk_mul]
  exact congrArg (Localization.mk _) (Subtype.ext rfl)

theorem sectionLinearEquiv_restrict (i j : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ pairOpen K i j) (c : pairRing K i j) :
    (twist K v).presheaf.map (homOfLE hU).op (sectionLinearEquiv K i j v c) =
      chartSectionEquiv K i v U (hU.trans (pairOpen_le_first K i j))
        ((plane K).presheaf.map (homOfLE hU).op (Proj.awayToSection (grading K) (X i * X j) c)) :=
  (chartSectionEquiv_restrict K i v (homOfLE hU) (pairOpen_le_first K i j)
    (Proj.awayToSection (grading K) (X i * X j) c)).symm

end Cylinder.GlobalTwistPairSections

end
