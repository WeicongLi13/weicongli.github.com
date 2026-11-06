module

public import Cylinder.BMMFourTupleCoordinates
public import Cylinder.BMMCoordinateFibers

/-! The actual diagonal through the first white point and the base
black point contains no other black point. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFourTupleDiagonalBlocker

set_option backward.isDefEq.respectTransparency false

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMBlackLineBlocks
open Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates
open Cylinder.BMMCoordinateFibers Cylinder.BMMWhiteBlackLine

variable {K : Type*} [Field K]

def diagonalRow (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) : Fin 3 → K :=
  coordinateRow g 0 - coordinateRow g 1

theorem diagonalRow_apply (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : Fin 3 → K) :
    dot (diagonalRow g) v = g v 0 - g v 1 := by
  have he : dot (diagonalRow g) v = dot (coordinateRow g 0) v - dot (coordinateRow g 1) v := by
    simp [diagonalRow, dot, sub_mul, Finset.sum_sub_distrib]
  rw [he, coordinateRow_apply, coordinateRow_apply]

theorem diagonalRow_nonzero (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) : diagonalRow g ≠ 0 := by
  intro hz
  have he := diagonalRow_apply g (g.symm (![1, 0, 0] : Fin 3 → K))
  rw [hz, LinearEquiv.apply_symm_apply] at he
  have h01 : (0 : K) = 1 := by simpa [dot] using he
  exact zero_ne_one h01

theorem diagonal_secant_is_base (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0)
    (P Q : A.W) (hPQ : P ≠ Q)
    (hdiag : blackFrame A T hcap (A.E P + A.E Q) 0 =
      blackFrame A T hcap (A.E P + A.E Q) 1) : secant A P Q hPQ = R := by
  let g := blackFrame A T hcap
  let l := diagonalRow g
  have hl : l ≠ 0 := diagonalRow_nonzero g
  obtain ⟨a, c, _ha, _hc, _hca, _hca', hP, _hQ, _hU, _hV⟩ :=
    actual_four_white_coordinates A T hcap htwo
  have hwhite : dot l T.P.val.rep = 0 := by
    apply (height_zero_iff A l T.P).mp
    change dot l (A.E T.P) = 0
    rw [diagonalRow_apply]
    change whiteVectors A T hcap 0 0 - whiteVectors A T hcap 0 1 = 0
    rw [hP]
    exact sub_self a
  have hR : dot l R.val.rep = 0 := by
    rw [diagonalRow_apply]
    change blackFrame A T hcap R.val.rep 0 - blackFrame A T hcap R.val.rep 1 = 0
    rw [blackFrame_base]
    simp
  obtain ⟨b, hb, hsum⟩ := A.sums P Q hPQ
  have hS : dot l (secant A P Q hPQ).val.rep = 0 := by
    have hzero : dot l (A.E P + A.E Q) = 0 := by
      rw [diagonalRow_apply]
      exact sub_eq_zero.mpr hdiag
    change Cylinder.BlackProjectionRationalLines.dotMap l (A.E P + A.E Q) = 0 at hzero
    rw [hsum, map_smul, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hb
  exact black_points_on_white_line_eq (configuration A) l hl T.P hwhite
    (secant A P Q hPQ) R hS hR

theorem diagonal_pair_sum_coordinate_zero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0)
    (P Q : A.W) (hPQ : P ≠ Q)
    (hdiag : blackFrame A T hcap (A.E P + A.E Q) 0 =
      blackFrame A T hcap (A.E P + A.E Q) 1) :
    blackFrame A T hcap (A.E P + A.E Q) 0 = 0 := by
  have hS := diagonal_secant_is_base A T hcap htwo P Q hPQ hdiag
  obtain ⟨b, _hb, hsum⟩ := A.sums P Q hPQ
  change A.E P + A.E Q = b • (secant A P Q hPQ).val.rep at hsum
  rw [hS] at hsum
  rw [hsum, map_smul, blackFrame_base]
  simp

end Cylinder.BMMFourTupleDiagonalBlocker

end
