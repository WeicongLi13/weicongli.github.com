module

public import Cylinder.BMMFourSecantWhiteCoordinates
public import Cylinder.BMMFourTupleDiagonalBlocker
public import Cylinder.BMMPrimeFourTupleCoordinates

/-! The additional actual white points exclude two four-point black
axes. The case where the two constructed points coincide is checked too. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBothFourImpossible

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BMMFourTupleBlackGeometry Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates
open Cylinder.BMMCoordinateFibers Cylinder.BMMFourSecantWhiteCoordinates
open Cylinder.BMMFourTupleDiagonalBlocker Cylinder.BMMFinitePlaneArcBound

variable {K : Type*} [Field K]

theorem not_both_four (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0) :
    ¬ ((coordinateBlacks A (blackFrame A T hcap) 1).card = 4 ∧
      (coordinateBlacks A (blackFrame A T hcap) 0).card = 4) := by
  rintro ⟨hy, hx⟩
  obtain ⟨a, c, ha, _hc, _hshift, hca, hP, hQ, hU, hV⟩ :=
    actual_four_white_coordinates A T hcap htwo
  change blackFrame A T hcap (A.E T.P) = _ at hP
  change blackFrame A T hcap (A.E T.Q) = _ at hQ
  change blackFrame A T hcap (A.E T.U) = _ at hU
  change blackFrame A T hcap (A.E T.V) = _ at hV
  obtain ⟨Dy⟩ := y_four_completion_exists A T hcap htwo hy
  obtain ⟨Dx⟩ := x_four_completion_exists A T hcap htwo hx
  have hDy := (four_completion_y_coordinates A T hcap Dy a c ha htwo hP hQ hU hV).1
  have hDx := (four_completion_x_coordinates A T hcap Dx a c ha htwo hP hQ hU hV).1
  by_cases heq : Dy.X = Dx.X
  · have he := congrFun (hDy.symm.trans (heq ▸ hDx)) 0
    change 3 * a - 4 * c = a at he
    have hne : T.P ≠ Dy.X := by
      intro hp
      have hz := congrFun (hP.symm.trans (hp ▸ hDy)) 2
      change c = 2 * a - c at hz
      have hzero : 2 * (c - a) = 0 := by linear_combination hz
      exact hca ((mul_eq_zero.mp hzero).resolve_left htwo)
    have hdiag : blackFrame A T hcap (A.E T.P + A.E Dy.X) 0 =
        blackFrame A T hcap (A.E T.P + A.E Dy.X) 1 := by
      rw [map_add, hP, hDy]
      change a + (3 * a - 4 * c) = a + a
      linear_combination he
    have hz := diagonal_pair_sum_coordinate_zero A T hcap htwo T.P Dy.X hne hdiag
    rw [map_add, hP, hDy] at hz
    have hzero : 2 * a = 0 := by
      change a + (3 * a - 4 * c) = 0 at hz
      linear_combination hz - he
    exact ha ((mul_eq_zero.mp hzero).resolve_left htwo)
  · have hdiag : blackFrame A T hcap (A.E Dy.X + A.E Dx.X) 0 =
        blackFrame A T hcap (A.E Dy.X + A.E Dx.X) 1 := by
      rw [map_add, hDy, hDx]
      change (3 * a - 4 * c) + a = a + (3 * a - 4 * c)
      ring
    have hz := diagonal_pair_sum_coordinate_zero A T hcap htwo Dy.X Dx.X heq hdiag
    rw [map_add, hDy, hDx] at hz
    have hzero : 2 * (2 * (c - a)) = 0 := by
      change (3 * a - 4 * c) + a = 0 at hz
      linear_combination -hz
    have hzero' := (mul_eq_zero.mp hzero).resolve_left htwo
    exact hca ((mul_eq_zero.mp hzero').resolve_left htwo)

theorem prime_not_both_four (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    ¬ ((coordinateBlacks A (BMMPrimeFourTupleCoordinates.primeBlackFrame p hp A T) 1).card = 4 ∧
      (coordinateBlacks A (BMMPrimeFourTupleCoordinates.primeBlackFrame p hp A T) 0).card = 4) := by
  exact not_both_four A T (BMMBlackLineCapFour.normalized_black_line_cap_four p hp A)
    (prime_two_nonzero p hp)

end Cylinder.BMMBothFourImpossible

end
