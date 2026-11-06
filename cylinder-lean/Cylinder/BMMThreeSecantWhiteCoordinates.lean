module

public import Cylinder.BMMThreeSecantMatchings
public import Cylinder.BMMFourTupleCoordinates

/-! The two remaining white points are obtained from the actual matching
on a three-point black line.  All coordinates use the original black frame. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMThreeSecantWhiteCoordinates

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlockerPairs
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMCoordinateFibers Cylinder.BMMThreeSecantMatchings
open Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates

variable {K : Type*} [Field K]

theorem sum_on_black (A : NormalizedSystem K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P Q : A.W) (hPQ : P ≠ Q)
    (B : A.B) (hcol : Collinear P.val Q.val B.val) :
    ∃ k : K, k ≠ 0 ∧ g (A.E P) + g (A.E Q) = k • g B.val.rep := by
  obtain ⟨k, hk, hs⟩ := sum_coordinates A g P Q hPQ
  have heq : secant A P Q hPQ = B :=
    secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ B hcol
  rw [heq] at hs
  exact ⟨k, hk, hs⟩

theorem completion_y_coordinates (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : Completion A T) (a c : K)
    (hP : blackFrame A T hcap (A.E T.P) = ![a, a, c])
    (hQ : blackFrame A T hcap (A.E T.Q) = ![-a, -a, c - 2 * a])
    (hU : blackFrame A T hcap (A.E T.U) = ![a, -a, -c])
    (hV : blackFrame A T hcap (A.E T.V) = ![-a, a, -c]) :
    blackFrame A T hcap (A.E D.X) = ![a - 2 * c, a, 2 * a - c] ∧
      blackFrame A T hcap (A.E D.Y) = ![2 * c - a, -a, c] := by
  let g := blackFrame A T hcap
  obtain ⟨k1, _hk1, hs1⟩ := sum_on_black A g T.Q D.X D.hXQ.symm _ D.firstX
  obtain ⟨k2, _hk2, hs2⟩ := sum_on_black A g T.U D.X D.hXU.symm _ D.secondX
  obtain ⟨k3, _hk3, hs3⟩ := sum_on_black A g T.V D.Y D.hYV.symm _ D.firstY
  obtain ⟨k4, _hk4, hs4⟩ := sum_on_black A g T.P D.Y D.hYP.symm _ D.secondY
  change _ = k1 • blackFrame A T hcap (firstCross A T).val.rep at hs1
  change _ = k2 • blackFrame A T hcap (secondCross A T).val.rep at hs2
  change _ = k3 • blackFrame A T hcap (firstCross A T).val.rep at hs3
  change _ = k4 • blackFrame A T hcap (secondCross A T).val.rep at hs4
  rw [blackFrame_first, smul_smul] at hs1 hs3
  rw [blackFrame_second, smul_smul] at hs2 hs4
  have hXy : -a + g (A.E D.X) 1 = 0 := by
    simpa [g, hQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs1 1
  have hXz : c - 2 * a + g (A.E D.X) 2 = 0 := by
    simpa [g, hQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs1 2
  have hXxz : a + g (A.E D.X) 0 = -c + g (A.E D.X) 2 := by
    have hh := (congrFun hs2 0).trans (congrFun hs2 2).symm
    simpa [g, hU, Pi.add_apply] using hh
  have hYy : a + g (A.E D.Y) 1 = 0 := by
    simpa [g, hV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs3 1
  have hYz : -c + g (A.E D.Y) 2 = 0 := by
    simpa [g, hV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs3 2
  have hYxz : a + g (A.E D.Y) 0 = c + g (A.E D.Y) 2 := by
    have hh := (congrFun hs4 0).trans (congrFun hs4 2).symm
    simpa [g, hP, Pi.add_apply] using hh
  constructor
  · ext i
    fin_cases i
    · change g (A.E D.X) 0 = a - 2 * c
      linear_combination hXxz + hXz
    · change g (A.E D.X) 1 = a
      linear_combination hXy
    · change g (A.E D.X) 2 = 2 * a - c
      linear_combination hXz
  · ext i
    fin_cases i
    · change g (A.E D.Y) 0 = 2 * c - a
      linear_combination hYxz + hYz
    · change g (A.E D.Y) 1 = -a
      linear_combination hYy
    · change g (A.E D.Y) 2 = c
      linear_combination hYz

theorem completion_x_coordinates (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (D : Completion A (swapLast A T)) (a c : K)
    (hP : blackFrame A T hcap (A.E T.P) = ![a, a, c])
    (hQ : blackFrame A T hcap (A.E T.Q) = ![-a, -a, c - 2 * a])
    (hU : blackFrame A T hcap (A.E T.U) = ![a, -a, -c])
    (hV : blackFrame A T hcap (A.E T.V) = ![-a, a, -c]) :
    blackFrame A T hcap (A.E D.X) = ![a, a - 2 * c, 2 * a - c] ∧
      blackFrame A T hcap (A.E D.Y) = ![-a, 2 * c - a, c] := by
  let g := blackFrame A T hcap
  obtain ⟨k1, _hk1, hs1⟩ := sum_on_black A g _ D.X D.hXQ.symm _ D.firstX
  obtain ⟨k2, _hk2, hs2⟩ := sum_on_black A g _ D.X D.hXU.symm _ D.secondX
  obtain ⟨k3, _hk3, hs3⟩ := sum_on_black A g _ D.Y D.hYV.symm _ D.firstY
  obtain ⟨k4, _hk4, hs4⟩ := sum_on_black A g _ D.Y D.hYP.symm _ D.secondY
  change g (A.E T.Q) + g (A.E D.X) = k1 • blackFrame A T hcap (thirdCross A T).val.rep at hs1
  change g (A.E T.V) + g (A.E D.X) = k2 • blackFrame A T hcap (fourthCross A T).val.rep at hs2
  change g (A.E T.U) + g (A.E D.Y) = k3 • blackFrame A T hcap (thirdCross A T).val.rep at hs3
  change g (A.E T.P) + g (A.E D.Y) = k4 • blackFrame A T hcap (fourthCross A T).val.rep at hs4
  rw [blackFrame_third, smul_smul] at hs1 hs3
  rw [blackFrame_fourth, smul_smul] at hs2 hs4
  have hXx : -a + g (A.E D.X) 0 = 0 := by
    simpa [g, hQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs1 0
  have hXz : c - 2 * a + g (A.E D.X) 2 = 0 := by
    simpa [g, hQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs1 2
  have hXyz : a + g (A.E D.X) 1 = -c + g (A.E D.X) 2 := by
    have hh := (congrFun hs2 1).trans (congrFun hs2 2).symm
    simpa [g, hV, Pi.add_apply] using hh
  have hYx : a + g (A.E D.Y) 0 = 0 := by
    simpa [g, hU, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs3 0
  have hYz : -c + g (A.E D.Y) 2 = 0 := by
    simpa [g, hU, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hs3 2
  have hYyz : a + g (A.E D.Y) 1 = c + g (A.E D.Y) 2 := by
    have hh := (congrFun hs4 1).trans (congrFun hs4 2).symm
    simpa [g, hP, Pi.add_apply] using hh
  constructor
  · ext i
    fin_cases i
    · change g (A.E D.X) 0 = a
      linear_combination hXx
    · change g (A.E D.X) 1 = a - 2 * c
      linear_combination hXyz + hXz
    · change g (A.E D.X) 2 = 2 * a - c
      linear_combination hXz
  · ext i
    fin_cases i
    · change g (A.E D.Y) 0 = -a
      linear_combination hYx
    · change g (A.E D.Y) 1 = 2 * c - a
      linear_combination hYyz + hYz
    · change g (A.E D.Y) 2 = c
      linear_combination hYz

theorem y_completion_exists (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (htwo : (2 : K) ≠ 0)
    (hcard : (coordinateBlacks A (blackFrame A T hcap) 1).card = 3) :
    Nonempty (Completion A T) := by
  apply exists_completion A T (blackFrame A T hcap) 1 htwo hcard
  · simp [blackFrame_base]
  · simp [blackFrame_first, Pi.smul_apply, smul_eq_mul]
  · simp [blackFrame_second, Pi.smul_apply, smul_eq_mul]

theorem x_completion_exists (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4)
    (htwo : (2 : K) ≠ 0)
    (hcard : (coordinateBlacks A (blackFrame A T hcap) 0).card = 3) :
    Nonempty (Completion A (swapLast A T)) := by
  apply exists_completion A (swapLast A T) (blackFrame A T hcap) 0 htwo hcard
  · simp [blackFrame_base]
  · change blackFrame A T hcap (thirdCross A T).val.rep 0 = 0
    simp [blackFrame_third, Pi.smul_apply, smul_eq_mul]
  · change blackFrame A T hcap (fourthCross A T).val.rep 0 = 0
    simp [blackFrame_fourth, Pi.smul_apply, smul_eq_mul]

end Cylinder.BMMThreeSecantWhiteCoordinates

end
