module

public import Cylinder.PlaneLaurentFractionNormalForm
public import Cylinder.GlobalTwistPairFractions
public import Cylinder.CoordinateChartLaurent

/-! Every homogeneous Laurent piece on a pair of standard charts
constructs an actual section of the global twisting sheaf there.
The construction records its literal polynomial numerator and
coordinate denominator, together with the coefficient normal form. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.PairLaurentSectionConstruction

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateChartPermutation
open Cylinder.CoordinateChartLaurent Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistPairSections Cylinder.GlobalTwistPairFractions
open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentHomogeneous
open Cylinder.PlaneLaurentDenominatorClearing Cylinder.PlaneLaurentFractionPieces
open Cylinder.PlaneLaurentFractionNormalForm

variable (K : Type*) [Field K] [Infinite K]

theorem exists_section_of_piece (v : ℤ) (i j : Index) (hij : i ≠ j)
    (f : piece (K := K) v {coordinateNumber i, coordinateNumber j}) :
    ∃ (s : Γ(twist K v, pairOpen K i j)) (w : ℤ) (_hw : 0 ≤ w)
      (a b : ℕ) (H : integerForms K w),
      w - a - b = v ∧
        f.val = shift (negativeDenominator (coordinateNumber i) (coordinateNumber j) a b)
          ((globalPieceEquivForms K w).symm H).val ∧
        ∀ q : pairOpen K i j, s.val q =
          Localization.mk H.val ⟨X i ^ a * X j ^ b, denominator_avoids K i j a b q⟩ := by
  have hnum : coordinateNumber i ≠ coordinateNumber j := by
    intro h
    exact hij ((_root_.finSuccEquiv 2).symm.injective h)
  obtain ⟨w, hw, a, b, H, hd, hf⟩ :=
    exists_fraction_normal_form v (coordinateNumber i) (coordinateNumber j) hnum f
  have hH : H.val.IsHomogeneous w.toNat := by
    have h : H.val ∈ Cylinder.PlaneLaurentHomogeneous.integerForms K w := H.property
    have he : Cylinder.PlaneLaurentHomogeneous.integerForms K w =
        MvPolynomial.homogeneousSubmodule (Option (Fin 2)) K w.toNat := by
      exact if_pos hw
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (he.le h)
  have hdn : (w.toNat : ℤ) - a - b = v := by
    rw [Int.toNat_of_nonneg hw]
    exact hd
  refine ⟨fractionSection K i j v w.toNat a b H.val hH hdn, w, hw, a, b, H, hd, hf, ?_⟩
  intro q
  exact fractionSection_value K i j v w.toNat a b H.val hH hdn q

end Cylinder.PairLaurentSectionConstruction

end
