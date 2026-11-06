module

public import Cylinder.PairTorusCompatibility
public import Cylinder.PlaneLaurentTorusFractions
public import Cylinder.PairLaurentSectionConstruction

/-! Actual pair-chart sections have precisely the Laurent values
with possible poles in those coordinates. The correspondence uses
literal homogeneous polynomial fractions in the same torus. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PairLaurentTorusModel

open AlgebraicGeometry
open Cylinder.CoordinateChartPermutation Cylinder.CoordinateChartLaurent
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistPairSections
open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentCommonTorus
open Cylinder.PlaneLaurentHomogeneous Cylinder.PlaneLaurentFractionPieces
open Cylinder.PlaneLaurentTorusFractions Cylinder.CommonTorusFractions
open Cylinder.ChartTorusEvaluation Cylinder.PairTorusCompatibility

variable (K : Type*) [Field K] [Infinite K]

theorem literalFraction_negative_powers (i j : Index) (a b : ℕ)
    (H : CoordinateLaurentLocalization.PlaneRing K) :
    literalFraction K i j a b H =
      ((coordinateUnit K i ^ (-(a : ℤ)) * coordinateUnit K j ^ (-(b : ℤ)) : (TorusRing K)ˣ) :
        TorusRing K) * polynomialMap K H := by
  unfold literalFraction denominatorUnit
  rw [← zpow_natCast (coordinateUnit K i) a, ← zpow_natCast (coordinateUnit K j) b]
  simp only [mul_inv_rev, ← zpow_neg]
  congr 2
  exact mul_comm _ _

theorem exists_piece_of_section (v : ℤ) (i j : Index)
    (s : Γ(twist K v, pairOpen K i j)) :
    ∃ f : piece (K := K) v {coordinateNumber i, coordinateNumber j},
      commonPieceMap K v {coordinateNumber i, coordinateNumber j} f =
        PairTorusEvaluation.torusValue K i j v s := by
  obtain ⟨d, a, b, H, hH, hd, hs⟩ :=
    GlobalTwistPairFractionRepresentatives.exists_pair_fraction K i j v s
  subst v
  refine ⟨polynomialFractionPiece d a b (coordinateNumber i) (coordinateNumber j) H hH, ?_⟩
  rw [commonPieceMap_polynomialFractionPiece,
    torusValue_of_fraction K i j _ s a b H hs, literalFraction_negative_powers]

theorem exists_section_of_piece (v : ℤ) (i j : Index) (hij : i ≠ j)
    (f : piece (K := K) v {coordinateNumber i, coordinateNumber j}) :
    ∃ s : Γ(twist K v, pairOpen K i j),
      PairTorusEvaluation.torusValue K i j v s =
        commonPieceMap K v {coordinateNumber i, coordinateNumber j} f := by
  obtain ⟨s, w, hw, a, b, H, hd, hf, hs⟩ :=
    PairLaurentSectionConstruction.exists_section_of_piece K v i j hij f
  refine ⟨s, ?_⟩
  rw [torusValue_of_fraction K i j v s a b H.val hs, literalFraction_negative_powers]
  let g := (globalPieceEquivForms K w).symm H
  have hfg : (fractionPiece w (coordinateNumber i) (coordinateNumber j) a b g).val = f.val :=
    hf.symm
  have he := commonPieceMap_eq_iff K v f
    (show piece (K := K) v {coordinateNumber i, coordinateNumber j} from
      ⟨(fractionPiece w (coordinateNumber i) (coordinateNumber j) a b g).val,
        by rw [← hd]; exact (fractionPiece w _ _ a b g).property⟩)
  have hmap : commonPieceMap K v {coordinateNumber i, coordinateNumber j} f =
      commonPieceMap K v {coordinateNumber i, coordinateNumber j}
        ⟨(fractionPiece w (coordinateNumber i) (coordinateNumber j) a b g).val,
          by rw [← hd]; exact (fractionPiece w _ _ a b g).property⟩ := he.mpr hfg.symm
  rw [hmap]
  subst v
  rw [commonPieceMap_fractionPiece, LinearEquiv.apply_symm_apply]

end Cylinder.PairLaurentTorusModel

end
