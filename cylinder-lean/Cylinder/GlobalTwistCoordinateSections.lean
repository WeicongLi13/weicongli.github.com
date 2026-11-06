module

public import Cylinder.GlobalTwistChartSections
public import Cylinder.CoordinateChartPermutation

/-! For each of the three coordinates, actual sections of O(v) on
D(X_i) are the degree-zero coordinate localization, multiplied by the
literal X_i-frame. The equivalence respects the original K-action. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistCoordinateSections

open MvPolynomial AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev coordinateRing (i : Option (Fin 2)) :=
  HomogeneousLocalization.Away (grading K) (X i : PlaneRing K)

def constantFraction (i : Option (Fin 2)) (a : K) : coordinateRing K i :=
  HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) 0 (C a) (by simp)

theorem constantFraction_val (i : Option (Fin 2)) (a : K) :
    (constantFraction K i a).val = algebraMap K (Localization.Away (X i : PlaneRing K)) a := by
  rw [constantFraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  change IsLocalization.mk' (Localization.Away (X i : PlaneRing K)) (C a) 1 = _
  rw [IsLocalization.mk'_one]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K)
    (Localization.Away (X i : PlaneRing K)) a).symm

theorem smul_eq_constant_mul (i : Option (Fin 2)) (a : K) (c : coordinateRing K i) :
    a • c = constantFraction K i a * c := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, constantFraction_val]
  exact Algebra.smul_def _ _

def coordinateSection (i : Option (Fin 2)) (v : ℤ) (c : coordinateRing K i) :
    Γ(twist K v, coordinateOpen K i) :=
  chartSectionEquiv K i v (coordinateOpen K i) le_rfl
    (Proj.awayToSection (grading K) (X i) c)

def sectionEquiv (i : Option (Fin 2)) (v : ℤ) :
    coordinateRing K i ≃ Γ(twist K v, coordinateOpen K i) :=
  (Iso.commRingCatIsoToRingEquiv
    (Proj.basicOpenIsoAway (grading K) (X i) (isHomogeneous_X K i) zero_lt_one)).toEquiv.trans
      (chartSectionEquiv K i v (coordinateOpen K i) le_rfl).toEquiv

theorem sectionEquiv_apply (i : Option (Fin 2)) (v : ℤ) (c : coordinateRing K i) :
    sectionEquiv K i v c = coordinateSection K i v c := rfl

theorem coordinateSection_add (i : Option (Fin 2)) (v : ℤ) (c d : coordinateRing K i) :
    coordinateSection K i v (c + d) = coordinateSection K i v c + coordinateSection K i v d := by
  unfold coordinateSection
  rw [map_add, map_add]

theorem away_constant_value (i : Option (Fin 2)) (a : K) (q : coordinateOpen K i) :
    ((Proj.awayToSection (grading K) (X i) (constantFraction K i a)).val q).val =
      algebraMap K (FullLocal K q.val) a := by
  have he := GlobalTwistStandardFractions.away_mk_section_value K i 0 (C a) (by simp) q
  refine he.trans ?_
  change Localization.mk (C a) (1 : q.val.asHomogeneousIdeal.toIdeal.primeCompl) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (PlaneRing K) (FullLocal K q.val) a).symm

theorem coordinateSection_smul (i : Option (Fin 2)) (v : ℤ) (a : K) (c : coordinateRing K i) :
    coordinateSection K i v (a • c) = a • coordinateSection K i v c := by
  apply Subtype.ext
  funext q
  change (frame K i v (coordinateOpen K i) le_rfl).val q *
      ((Proj.awayToSection (grading K) (X i) (a • c)).val q).val =
    a • ((frame K i v (coordinateOpen K i) le_rfl).val q *
      ((Proj.awayToSection (grading K) (X i) c).val q).val)
  rw [smul_eq_constant_mul, map_mul, AlgebraicGeometry.Proj.mul_apply,
    HomogeneousLocalization.val_mul, away_constant_value, Algebra.smul_def]
  exact mul_left_comm _ _ _

def sectionLinearEquiv (i : Option (Fin 2)) (v : ℤ) :
    coordinateRing K i ≃ₗ[K] Γ(twist K v, coordinateOpen K i) where
  __ := sectionEquiv K i v
  map_add' := coordinateSection_add K i v
  map_smul' := coordinateSection_smul K i v

theorem sectionLinearEquiv_apply (i : Option (Fin 2)) (v : ℤ) (c : coordinateRing K i) :
    sectionLinearEquiv K i v c = coordinateSection K i v c := rfl

theorem sectionLinearEquiv_fraction (i : Option (Fin 2)) (v : ℤ) (m n : ℕ)
    (H : PlaneRing K) (hH : H ∈ grading K (m • (1 : ℕ))) (hd : (m : ℤ) - n = v)
    (q : coordinateOpen K i) :
    (sectionLinearEquiv K i v
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH)).val q =
        Localization.mk H ⟨X i ^ n,
          coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩ :=
  GlobalTwistStandardFractions.chartSectionEquiv_fraction K i v m n H hH hd q

theorem sectionLinearEquiv_restrict (i : Option (Fin 2)) (v : ℤ) (U : (plane K).Opens)
    (hU : U ≤ coordinateOpen K i) (c : coordinateRing K i) :
    (twist K v).presheaf.map (homOfLE hU).op (sectionLinearEquiv K i v c) =
      chartSectionEquiv K i v U hU
        ((plane K).presheaf.map (homOfLE hU).op (Proj.awayToSection (grading K) (X i) c)) :=
  (chartSectionEquiv_restrict K i v (homOfLE hU) le_rfl
    (Proj.awayToSection (grading K) (X i) c)).symm

end Cylinder.GlobalTwistCoordinateSections
end
