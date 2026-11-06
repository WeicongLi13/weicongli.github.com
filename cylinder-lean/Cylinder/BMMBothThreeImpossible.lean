module

public import Cylinder.BMMThreeSecantWhiteCoordinates
public import Cylinder.BMMFourTupleDiagonalBlocker
public import Cylinder.BMMPrimeFourTupleCoordinates

/-! A non-special four-tuple cannot give two three-point black lines.
The additional white points are constructed by the actual matchings. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBothThreeImpossible

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BMMFourTupleBlackGeometry Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates
open Cylinder.BMMCoordinateFibers Cylinder.BMMThreeSecantWhiteCoordinates
open Cylinder.BMMFourTupleDiagonalBlocker Cylinder.BMMFinitePlaneArcBound

variable {K : Type*} [Field K]

theorem not_both_three (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0) :
    ¬ ((coordinateBlacks A (blackFrame A T hcap) 1).card = 3 ∧
      (coordinateBlacks A (blackFrame A T hcap) 0).card = 3) := by
  rintro ⟨hy, hx⟩
  obtain ⟨a, c, _ha, hc, _hshift, hca, hP, hQ, hU, hV⟩ :=
    actual_four_white_coordinates A T hcap htwo
  change blackFrame A T hcap (A.E T.P) = _ at hP
  change blackFrame A T hcap (A.E T.Q) = _ at hQ
  change blackFrame A T hcap (A.E T.U) = _ at hU
  change blackFrame A T hcap (A.E T.V) = _ at hV
  obtain ⟨Dy⟩ := y_completion_exists A T hcap htwo hy
  obtain ⟨Dx⟩ := x_completion_exists A T hcap htwo hx
  have hDy := (completion_y_coordinates A T hcap Dy a c hP hQ hU hV).1
  have hDx := (completion_x_coordinates A T hcap Dx a c hP hQ hU hV).1
  have hne : Dy.X ≠ Dx.X := by
    intro heq
    have he := congrFun (hDy.symm.trans (heq ▸ hDx)) 0
    have hzero : 2 * c = 0 := by
      change a - 2 * c = a at he
      linear_combination -he
    exact hc ((mul_eq_zero.mp hzero).resolve_left htwo)
  have hdiag : blackFrame A T hcap (A.E Dy.X + A.E Dx.X) 0 =
      blackFrame A T hcap (A.E Dy.X + A.E Dx.X) 1 := by
    rw [map_add, hDy, hDx]
    change (a - 2 * c) + a = a + (a - 2 * c)
    ring
  have hz := diagonal_pair_sum_coordinate_zero A T hcap htwo Dy.X Dx.X hne hdiag
  rw [map_add, hDy, hDx] at hz
  have hzero : 2 * (c - a) = 0 := by
    change (a - 2 * c) + a = 0 at hz
    linear_combination -hz
  exact hca ((mul_eq_zero.mp hzero).resolve_left htwo)

theorem prime_not_both_three (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    ¬ ((coordinateBlacks A (BMMPrimeFourTupleCoordinates.primeBlackFrame p hp A T) 1).card = 3 ∧
      (coordinateBlacks A (BMMPrimeFourTupleCoordinates.primeBlackFrame p hp A T) 0).card = 3) := by
  exact not_both_three A T (BMMBlackLineCapFour.normalized_black_line_cap_four p hp A)
    (prime_two_nonzero p hp)

end Cylinder.BMMBothThreeImpossible

end
