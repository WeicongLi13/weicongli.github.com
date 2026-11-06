module

public import Cylinder.BMMFourSecantMatchings
public import Cylinder.BMMThreeSecantWhiteCoordinates
public import Cylinder.BMMFourSecantCoordinateAlgebra

/-! The actual four-secant matchings determine the additional white
vectors and the fourth black point, whose parameter is one half. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMFourSecantWhiteCoordinates

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlockerPairs
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMCoordinateFibers Cylinder.BMMFourSecantMatchings
open Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates
open Cylinder.BMMThreeSecantWhiteCoordinates Cylinder.BMMFourSecantCoordinateAlgebra

variable {K : Type*} [Field K]

def swapXY (v : Fin 3 → K) : Fin 3 → K := ![v 1, v 0, v 2]

theorem swapXY_add (v w : Fin 3 → K) : swapXY (v + w) = swapXY v + swapXY w := by
  ext i
  fin_cases i <;> rfl

theorem swapXY_smul (a : K) (v : Fin 3 → K) : swapXY (a • v) = a • swapXY v := by
  ext i
  fin_cases i <;> rfl

theorem axis_parameter_x (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : A.B) (hDR : D ≠ R) (hz : blackFrame A T hcap D.val.rep 0 = 0) :
    ∃ k b : K, k ≠ 0 ∧ blackFrame A T hcap D.val.rep = k • ![0, 1, b] := by
  let g := blackFrame A T hcap
  have hk : g D.val.rep 1 ≠ 0 := by
    intro h1
    have hv : g D.val.rep = g D.val.rep 2 • g R.val.rep := by
      rw [blackFrame_base]
      ext i
      fin_cases i
      · simpa [Pi.smul_apply, smul_eq_mul] using hz
      · simpa [Pi.smul_apply, smul_eq_mul] using h1
      · simp [Pi.smul_apply, smul_eq_mul]
    have he : D.val.rep = g D.val.rep 2 • R.val.rep := by
      apply g.injective
      simpa only [map_smul] using hv
    exact representatives_not_proportional R.val D.val
      (fun h => hDR (Subtype.ext h.symm)) _ he
  refine ⟨g D.val.rep 1, g D.val.rep 2 / g D.val.rep 1, hk, ?_⟩
  ext i
  fin_cases i
  · simpa [Pi.smul_apply, smul_eq_mul] using hz
  · simp [g, Pi.smul_apply, smul_eq_mul]
  · change g D.val.rep 2 = g D.val.rep 1 * (g D.val.rep 2 / g D.val.rep 1)
    field_simp

theorem axis_parameter_y (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : A.B) (hDR : D ≠ R) (hz : blackFrame A T hcap D.val.rep 1 = 0) :
    ∃ k b : K, k ≠ 0 ∧ blackFrame A T hcap D.val.rep = k • ![1, 0, b] := by
  let g := blackFrame A T hcap
  have hk : g D.val.rep 0 ≠ 0 := by
    intro h0
    have hv : g D.val.rep = g D.val.rep 2 • g R.val.rep := by
      rw [blackFrame_base]
      ext i
      fin_cases i
      · simpa [Pi.smul_apply, smul_eq_mul] using h0
      · simpa [Pi.smul_apply, smul_eq_mul] using hz
      · simp [Pi.smul_apply, smul_eq_mul]
    have he : D.val.rep = g D.val.rep 2 • R.val.rep := by
      apply g.injective
      simpa only [map_smul] using hv
    exact representatives_not_proportional R.val D.val
      (fun h => hDR (Subtype.ext h.symm)) _ he
  refine ⟨g D.val.rep 0, g D.val.rep 2 / g D.val.rep 0, hk, ?_⟩
  ext i
  fin_cases i
  · simp [g, Pi.smul_apply, smul_eq_mul]
  · simpa [Pi.smul_apply, smul_eq_mul] using hz
  · change g D.val.rep 2 = g D.val.rep 0 * (g D.val.rep 2 / g D.val.rep 0)
    field_simp

theorem four_completion_x_coordinates (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : FourCompletion A (swapLast A T) (blackFrame A T hcap) 0) (a c : K)
    (ha : a ≠ 0) (htwo : (2 : K) ≠ 0)
    (hP : blackFrame A T hcap (A.E T.P) = ![a, a, c])
    (hQ : blackFrame A T hcap (A.E T.Q) = ![-a, -a, c - 2 * a])
    (hU : blackFrame A T hcap (A.E T.U) = ![a, -a, -c])
    (hV : blackFrame A T hcap (A.E T.V) = ![-a, a, -c]) :
    blackFrame A T hcap (A.E D.X) = ![a, 3 * a - 4 * c, 2 * a - c] ∧
      blackFrame A T hcap (A.E D.Y) = ![-a, 4 * c - a, c] ∧
      ∃ k : K, k ≠ 0 ∧ blackFrame A T hcap D.D.val.rep = k • ![0, 1, (2 : K)⁻¹] := by
  let g := blackFrame A T hcap
  obtain ⟨k, b, hk, hD⟩ := axis_parameter_x A T hcap D.D D.ne_base D.zero
  obtain ⟨k1, _hk1, hs1⟩ := sum_on_black A g _ D.X D.hXQ.symm _ D.firstX
  obtain ⟨k2, _hk2, hs2⟩ := sum_on_black A g _ D.Y D.hYV.symm _ D.firstY
  obtain ⟨k3, _hk3, hs3⟩ := sum_on_black A g D.X D.Y D.hXY _ D.secondXY
  obtain ⟨k4, _hk4, hs4⟩ := sum_on_black A g _ D.X D.hXU.symm _ D.fourthUX
  obtain ⟨k5, _hk5, hs5⟩ := sum_on_black A g D.Y _ D.hYP _ D.fourthYP
  change g (A.E T.Q) + g (A.E D.X) = k1 • blackFrame A T hcap (thirdCross A T).val.rep at hs1
  change g (A.E T.U) + g (A.E D.Y) = k2 • blackFrame A T hcap (thirdCross A T).val.rep at hs2
  change _ = k3 • blackFrame A T hcap (fourthCross A T).val.rep at hs3
  rw [blackFrame_third, smul_smul] at hs1 hs2
  rw [blackFrame_fourth, smul_smul] at hs3
  change _ = k4 • blackFrame A T hcap D.D.val.rep at hs4
  change _ = k5 • blackFrame A T hcap D.D.val.rep at hs5
  rw [hD, smul_smul] at hs4 hs5
  change g (A.E T.V) + g (A.E D.X) = _ at hs4
  change g (A.E D.Y) + g (A.E T.P) = _ at hs5
  have hs2' := hs2
  rw [add_comm] at hs2'
  obtain ⟨hX, hY, hb⟩ := extra_white_coordinates a c b ha htwo (g (A.E D.X)) (g (A.E D.Y))
    _ _ _ _ _ (by simpa only [g, hQ] using hs1)
    (by simpa only [g, hU] using hs2') hs3
    (by simpa only [g, hV] using hs4) (by simpa only [g, hP] using hs5)
  exact ⟨hX, hY, k, hk, hb ▸ hD⟩

theorem four_completion_y_coordinates (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : FourCompletion A T (blackFrame A T hcap) 1) (a c : K)
    (ha : a ≠ 0) (htwo : (2 : K) ≠ 0)
    (hP : blackFrame A T hcap (A.E T.P) = ![a, a, c])
    (hQ : blackFrame A T hcap (A.E T.Q) = ![-a, -a, c - 2 * a])
    (hU : blackFrame A T hcap (A.E T.U) = ![a, -a, -c])
    (hV : blackFrame A T hcap (A.E T.V) = ![-a, a, -c]) :
    blackFrame A T hcap (A.E D.X) = ![3 * a - 4 * c, a, 2 * a - c] ∧
      blackFrame A T hcap (A.E D.Y) = ![4 * c - a, -a, c] ∧
      ∃ k : K, k ≠ 0 ∧ blackFrame A T hcap D.D.val.rep = k • ![1, 0, (2 : K)⁻¹] := by
  let g := blackFrame A T hcap
  obtain ⟨k, b, hk, hD⟩ := axis_parameter_y A T hcap D.D D.ne_base D.zero
  obtain ⟨k1, _hk1, hs1⟩ := sum_on_black A g _ D.X D.hXQ.symm _ D.firstX
  obtain ⟨k2, _hk2, hs2⟩ := sum_on_black A g _ D.Y D.hYV.symm _ D.firstY
  obtain ⟨k3, _hk3, hs3⟩ := sum_on_black A g D.X D.Y D.hXY _ D.secondXY
  obtain ⟨k4, _hk4, hs4⟩ := sum_on_black A g _ D.X D.hXU.symm _ D.fourthUX
  obtain ⟨k5, _hk5, hs5⟩ := sum_on_black A g D.Y _ D.hYP _ D.fourthYP
  change _ = k1 • blackFrame A T hcap (firstCross A T).val.rep at hs1
  change _ = k2 • blackFrame A T hcap (firstCross A T).val.rep at hs2
  change _ = k3 • blackFrame A T hcap (secondCross A T).val.rep at hs3
  rw [blackFrame_first, smul_smul] at hs1 hs2
  rw [blackFrame_second, smul_smul] at hs3
  change _ = k4 • blackFrame A T hcap D.D.val.rep at hs4
  change _ = k5 • blackFrame A T hcap D.D.val.rep at hs5
  rw [hD, smul_smul] at hs4 hs5
  have t1 := congrArg swapXY hs1
  have t2 := congrArg swapXY hs2
  have t3 := congrArg swapXY hs3
  have t4 := congrArg swapXY hs4
  have t5 := congrArg swapXY hs5
  simp only [swapXY_add, swapXY_smul] at t1 t2 t3 t4 t5
  rw [add_comm] at t2
  obtain ⟨hX, hY, hb⟩ := extra_white_coordinates a c b ha htwo
    (swapXY (g (A.E D.X))) (swapXY (g (A.E D.Y))) _ _ _ _ _
    (by simpa [g, hQ, swapXY] using t1)
    (by simpa [g, hV, swapXY] using t2)
    (by exact t3)
    (by simpa [g, hU, swapXY] using t4)
    (by simpa [g, hP, swapXY] using t5)
  refine ⟨?_, ?_, k, hk, hb ▸ hD⟩
  · ext j
    fin_cases j
    · exact congrFun hX 1
    · exact congrFun hX 0
    · exact congrFun hX 2
  · ext j
    fin_cases j
    · exact congrFun hY 1
    · exact congrFun hY 0
    · exact congrFun hY 2

theorem x_four_completion_exists (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0)
    (hcard : (coordinateBlacks A (blackFrame A T hcap) 0).card = 4) :
    Nonempty (FourCompletion A (swapLast A T) (blackFrame A T hcap) 0) := by
  apply exists_four_completion A (swapLast A T) (blackFrame A T hcap) 0 htwo hcard
  · simp [blackFrame_base]
  · change blackFrame A T hcap (thirdCross A T).val.rep 0 = 0
    simp [blackFrame_third, Pi.smul_apply, smul_eq_mul]
  · change blackFrame A T hcap (fourthCross A T).val.rep 0 = 0
    simp [blackFrame_fourth, Pi.smul_apply, smul_eq_mul]

theorem y_four_completion_exists (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (htwo : (2 : K) ≠ 0)
    (hcard : (coordinateBlacks A (blackFrame A T hcap) 1).card = 4) :
    Nonempty (FourCompletion A T (blackFrame A T hcap) 1) := by
  apply exists_four_completion A T (blackFrame A T hcap) 1 htwo hcard
  · simp [blackFrame_base]
  · simp [blackFrame_first, Pi.smul_apply, smul_eq_mul]
  · simp [blackFrame_second, Pi.smul_apply, smul_eq_mul]

end Cylinder.BMMFourSecantWhiteCoordinates

end
