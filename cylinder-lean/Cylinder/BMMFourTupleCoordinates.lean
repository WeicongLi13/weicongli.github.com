module

public import Cylinder.BMMFourTupleFrame
public import Cylinder.BMMFourTupleCoordinateAlgebra

/-! The actual white coordinates follow from the six true normalized
secant sums and the previously constructed black-point frame. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMFourTupleCoordinates

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BMMFourTupleBlackGeometry Cylinder.BMMFourTupleFrame
open Cylinder.BMMFourTupleCoordinateAlgebra

variable {K : Type*} [Field K]

def whitePoints (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : Fin 4 → A.W := ![T.P, T.Q, T.U, T.V]

def whiteVectors (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) : Fin 4 → Fin 3 → K :=
  fun i => blackFrame A T hcap (A.E (whitePoints A T i))

theorem sum_coordinates (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q : A.W) (hPQ : P ≠ Q) :
    ∃ a : K, a ≠ 0 ∧ g (A.E P) + g (A.E Q) = a • g (secant A P Q hPQ).val.rep := by
  obtain ⟨a, ha, h⟩ := A.sums P Q hPQ
  refine ⟨a, ha, ?_⟩
  rw [← map_add, h, map_smul]

theorem exists_six_sum_coefficients (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    ∃ a12 a34 a13 a14 a24 a23 : K,
      a12 ≠ 0 ∧ a34 ≠ 0 ∧ a13 ≠ 0 ∧ a14 ≠ 0 ∧ a24 ≠ 0 ∧ a23 ≠ 0 ∧
      (whiteVectors A T hcap 0 + whiteVectors A T hcap 1 = a12 • ![0, 0, 1]) ∧
      (whiteVectors A T hcap 2 + whiteVectors A T hcap 3 = a34 • ![0, 0, 1]) ∧
      (whiteVectors A T hcap 0 + whiteVectors A T hcap 2 = a13 • ![1, 0, 0]) ∧
      (whiteVectors A T hcap 0 + whiteVectors A T hcap 3 = a14 • ![0, 1, 0]) ∧
      (whiteVectors A T hcap 1 + whiteVectors A T hcap 3 = a24 • ![1, 0, 1]) ∧
      whiteVectors A T hcap 1 + whiteVectors A T hcap 2 = a23 • ![0, 1, 1] := by
  let g := blackFrame A T hcap
  obtain ⟨a12, ha12, h12⟩ := sum_coordinates A g T.P T.Q T.hPQ
  obtain ⟨a34, ha34, h34⟩ := sum_coordinates A g T.U T.V T.hUV
  obtain ⟨a13, ha13, h13⟩ := sum_coordinates A g T.P T.U T.hPU
  obtain ⟨a14, ha14, h14⟩ := sum_coordinates A g T.P T.V T.hPV
  obtain ⟨a24, ha24, h24⟩ := sum_coordinates A g T.Q T.V T.hQV
  obtain ⟨a23, ha23, h23⟩ := sum_coordinates A g T.Q T.U T.hQU
  have hb12 : secant A T.P T.Q T.hPQ = R := first_blocker (configuration A) A.E R T
  have hb34 : secant A T.U T.V T.hUV = R := second_blocker (configuration A) A.E R T
  rw [hb12] at h12
  rw [hb34] at h34
  change blackFrame A T hcap (A.E T.P) + blackFrame A T hcap (A.E T.Q) =
    a12 • blackFrame A T hcap R.val.rep at h12
  change blackFrame A T hcap (A.E T.U) + blackFrame A T hcap (A.E T.V) =
    a34 • blackFrame A T hcap R.val.rep at h34
  rw [blackFrame_base] at h12 h34
  change _ = a13 • blackFrame A T hcap (firstCross A T).val.rep at h13
  change _ = a14 • blackFrame A T hcap (thirdCross A T).val.rep at h14
  change _ = a24 • blackFrame A T hcap (secondCross A T).val.rep at h24
  change _ = a23 • blackFrame A T hcap (fourthCross A T).val.rep at h23
  rw [blackFrame_first, smul_smul] at h13
  rw [blackFrame_third, smul_smul] at h14
  rw [blackFrame_second, smul_smul] at h24
  rw [blackFrame_fourth, smul_smul] at h23
  exact ⟨a12, a34, a13 * xScale A T hcap, a14 * yScale A T hcap,
    a24 * baseFrame A T hcap (secondCross A T).val.rep 2,
    a23 * baseFrame A T hcap (fourthCross A T).val.rep 2,
    ha12, ha34, mul_ne_zero ha13 (xScale_nonzero A T hcap),
    mul_ne_zero ha14 (yScale_nonzero A T hcap),
    mul_ne_zero ha24 (second_coordinates_nonzero A T hcap).2,
    mul_ne_zero ha23 (fourth_coordinates_nonzero A T hcap).2,
    h12, h34, h13, h14, h24, h23⟩

theorem actual_four_white_coordinates (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0) :
    ∃ a c : K, a ≠ 0 ∧ c ≠ 0 ∧ c - 2 * a ≠ 0 ∧ c - a ≠ 0 ∧
      whiteVectors A T hcap 0 = ![a, a, c] ∧
      whiteVectors A T hcap 1 = ![-a, -a, c - 2 * a] ∧
      whiteVectors A T hcap 2 = ![a, -a, -c] ∧
      whiteVectors A T hcap 3 = ![-a, a, -c] := by
  obtain ⟨a12, _a34, _a13, _a14, _a24, _a23, ha12, _ha34, _ha13, _ha14,
    _ha24, _ha23, h12, h34, h13, h14, h24, h23⟩ := exists_six_sum_coefficients A T hcap
  obtain ⟨a, c, h0, h1, h2, h3⟩ := four_white_coordinates (whiteVectors A T hcap) htwo
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h12 0)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h12 1)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h34 0)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h13 1)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h13 2)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h14 0)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h14 2)
    (by simpa [Pi.smul_apply, smul_eq_mul] using congrFun h24 1)
    ((congrFun h24 0).trans (congrFun h24 2).symm)
    ((congrFun h23 1).trans (congrFun h23 2).symm)
  have ha : a ≠ 0 := by
    have h := normalized_white_coordinates_nonzero A T hcap T.P 0
    change whiteVectors A T hcap 0 0 ≠ 0 at h
    rwa [h0] at h
  have hc : c ≠ 0 := by
    have h := normalized_white_coordinates_nonzero A T hcap T.P 2
    change whiteVectors A T hcap 0 2 ≠ 0 at h
    rwa [h0] at h
  have hshift : c - 2 * a ≠ 0 := by
    have h := normalized_white_coordinates_nonzero A T hcap T.Q 2
    change whiteVectors A T hcap 1 2 ≠ 0 at h
    rwa [h1] at h
  have hca : c - a ≠ 0 := by
    intro hca
    have hsame : c = a := sub_eq_zero.mp hca
    have hs := congrFun h12 2
    rw [h0, h1] at hs
    have hs' : c + (c - 2 * a) = a12 := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hs
    rw [hsame] at hs'
    apply ha12
    linear_combination -hs'
  exact ⟨a, c, ha, hc, hshift, hca, h0, h1, h2, h3⟩

end Cylinder.BMMFourTupleCoordinates

end
