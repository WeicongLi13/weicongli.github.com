module

public import Cylinder.BMMFourTupleBlackGeometry
public import Cylinder.BMMWhiteBlackLine
public import Cylinder.ConicAffineMaps

/-! A genuine basis from the five black points of a non-special tuple.
The two opposite black points determine the two nonzero scale factors
of the final coordinate equivalence. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFourTupleFrame

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMTriangleFrame Cylinder.BMMFrameRatios Cylinder.ConicAffineMaps
open Cylinder.BMMWhiteBlackLine

variable {K : Type*} [Field K]

def basisPoints (A : NormalizedSystem K) {R : A.B} (T : FourTuple (configuration A) A.E R) :
    Fin 3 → A.B := ![firstCross A T, thirdCross A T, R]

abbrev basisVectors (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : Fin 3 → Fin 3 → K :=
  fun i => (basisPoints A T i).val.rep

theorem basisPoints_injective (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : Function.Injective (basisPoints A T) := by
  have h01 := first_ne_third A T
  have h20 := base_ne_first A T
  have h21 := base_ne_third A T
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [basisPoints]

theorem triple_cycle (v w x : Fin 3 → K) : dot (cross v w) x = dot (cross w x) v := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

theorem basis_determinant_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    determinant (basisVectors A T) ≠ 0 := by
  intro hz
  have hcyc : determinant (basisVectors A T) =
      dot (cross R.val.rep (firstCross A T).val.rep) (thirdCross A T).val.rep := by
    exact (triple_cycle (firstCross A T).val.rep (thirdCross A T).val.rep R.val.rep).trans
      (triple_cycle (thirdCross A T).val.rep R.val.rep (firstCross A T).val.rep)
  have hcol : dot (cross R.val.rep (firstCross A T).val.rep) (thirdCross A T).val.rep = 0 :=
    hcyc.symm.trans hz
  obtain ⟨u, _hu, heq⟩ := annihilator_proportional
    (cross R.val.rep (firstCross A T).val.rep) R.val.rep (thirdCross A T).val.rep
    (first_line_coefficients_nonzero A T) (second_line_coefficients_nonzero A T)
    (dot_cross_left _ _) hcol
  apply black_lines_distinct_of_cap_four A T hcap
  exact (Projectivization.mk_eq_mk_iff' K _ _
    (first_line_coefficients_nonzero A T) (second_line_coefficients_nonzero A T)).mpr ⟨u, heq.symm⟩

abbrev baseFrame (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  coordinates (basisVectors A T) (basis_determinant_nonzero A T hcap)

theorem baseFrame_base (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap R.val.rep = (Pi.single 2 1 : Fin 3 → K) :=
  coordinates_basis (basisVectors A T) (basis_determinant_nonzero A T hcap) 2

theorem baseFrame_first (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (firstCross A T).val.rep = (Pi.single 0 1 : Fin 3 → K) :=
  coordinates_basis (basisVectors A T) (basis_determinant_nonzero A T hcap) 0

theorem baseFrame_third (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (thirdCross A T).val.rep = (Pi.single 1 1 : Fin 3 → K) :=
  coordinates_basis (basisVectors A T) (basis_determinant_nonzero A T hcap) 1

theorem second_coordinate_zero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (secondCross A T).val.rep 1 = 0 :=
  (coordinate_zero_iff (basisVectors A T) (basis_determinant_nonzero A T hcap) _ 1).mpr
    (opposite_black_triple_collinear A T)

theorem fourth_coordinate_zero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (fourthCross A T).val.rep 0 = 0 :=
  (coordinate_zero_iff (basisVectors A T) (basis_determinant_nonzero A T hcap) _ 0).mpr
    (collinear_swap _ _ _ (other_opposite_black_triple_collinear A T))

theorem second_coordinates_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (secondCross A T).val.rep 0 ≠ 0 ∧
      baseFrame A T hcap (secondCross A T).val.rep 2 ≠ 0 := by
  have h1 := second_coordinate_zero A T hcap
  constructor
  · intro h0
    have hprop := coordinates_two_zeros_previous (basisVectors A T)
      (basis_determinant_nonzero A T hcap) (secondCross A T).val.rep 1 h1 h0
    exact representatives_not_proportional R.val (secondCross A T).val
      (fun h => base_ne_second A T (Subtype.ext h)) _ hprop
  · intro h2
    have hprop := coordinates_two_zeros (basisVectors A T)
      (basis_determinant_nonzero A T hcap) (secondCross A T).val.rep 1 h1 h2
    exact representatives_not_proportional (firstCross A T).val (secondCross A T).val
      (fun h => opposite_secants_ne A T (Subtype.ext h)) _ hprop

theorem fourth_coordinates_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    baseFrame A T hcap (fourthCross A T).val.rep 1 ≠ 0 ∧
      baseFrame A T hcap (fourthCross A T).val.rep 2 ≠ 0 := by
  have h0 := fourth_coordinate_zero A T hcap
  constructor
  · intro h1
    have hprop := coordinates_two_zeros (basisVectors A T)
      (basis_determinant_nonzero A T hcap) (fourthCross A T).val.rep 0 h0 h1
    exact representatives_not_proportional R.val (fourthCross A T).val
      (fun h => base_ne_fourth A T (Subtype.ext h)) _ hprop
  · intro h2
    have hprop := coordinates_two_zeros_previous (basisVectors A T)
      (basis_determinant_nonzero A T hcap) (fourthCross A T).val.rep 0 h0 h2
    exact representatives_not_proportional (thirdCross A T).val (fourthCross A T).val
      (fun h => other_opposite_secants_ne A T (Subtype.ext h)) _ hprop

def xScale (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) : K :=
  baseFrame A T hcap (secondCross A T).val.rep 2 /
    baseFrame A T hcap (secondCross A T).val.rep 0

def yScale (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) : K :=
  baseFrame A T hcap (fourthCross A T).val.rep 2 /
    baseFrame A T hcap (fourthCross A T).val.rep 1

theorem xScale_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) : xScale A T hcap ≠ 0 :=
  div_ne_zero (second_coordinates_nonzero A T hcap).2 (second_coordinates_nonzero A T hcap).1

theorem yScale_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) : yScale A T hcap ≠ 0 :=
  div_ne_zero (fourth_coordinates_nonzero A T hcap).2 (fourth_coordinates_nonzero A T hcap).1

def blackFrame (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  (baseFrame A T hcap).trans (affineCoordinates (xScale A T hcap) (yScale A T hcap) 0 0 0
    (xScale_nonzero A T hcap) (yScale_nonzero A T hcap))

theorem blackFrame_apply (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (v : Fin 3 → K) :
    blackFrame A T hcap v =
      ![xScale A T hcap * baseFrame A T hcap v 0,
        yScale A T hcap * baseFrame A T hcap v 1, baseFrame A T hcap v 2] := by
  simp [blackFrame, affineCoordinates, affineVector, LinearEquiv.trans_apply]

theorem blackFrame_base (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    blackFrame A T hcap R.val.rep = (![0, 0, 1] : Fin 3 → K) := by
  rw [blackFrame_apply, baseFrame_base]
  simp [Pi.single_apply]

theorem blackFrame_first (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    blackFrame A T hcap (firstCross A T).val.rep =
      xScale A T hcap • (![1, 0, 0] : Fin 3 → K) := by
  rw [blackFrame_apply, baseFrame_first]
  ext i
  fin_cases i <;> simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]

theorem blackFrame_third (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    blackFrame A T hcap (thirdCross A T).val.rep =
      yScale A T hcap • (![0, 1, 0] : Fin 3 → K) := by
  rw [blackFrame_apply, baseFrame_third]
  ext i
  fin_cases i <;> simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]

theorem blackFrame_second (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    blackFrame A T hcap (secondCross A T).val.rep =
      baseFrame A T hcap (secondCross A T).val.rep 2 • (![1, 0, 1] : Fin 3 → K) := by
  rw [blackFrame_apply]
  ext i
  fin_cases i
  · simp [xScale, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (second_coordinates_nonzero A T hcap).1]
  · simp [Pi.smul_apply, smul_eq_mul, second_coordinate_zero A T hcap]
  · simp [Pi.smul_apply, smul_eq_mul]

theorem blackFrame_fourth (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    blackFrame A T hcap (fourthCross A T).val.rep =
      baseFrame A T hcap (fourthCross A T).val.rep 2 • (![0, 1, 1] : Fin 3 → K) := by
  rw [blackFrame_apply]
  ext i
  fin_cases i
  · simp [Pi.smul_apply, smul_eq_mul, fourth_coordinate_zero A T hcap]
  · simp [yScale, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (fourth_coordinates_nonzero A T hcap).1]
  · simp [Pi.smul_apply, smul_eq_mul]

theorem base_white_coordinates_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (P : A.W) :
    ∀ i, baseFrame A T hcap P.val.rep i ≠ 0 := by
  intro i hz
  have hraw := (coordinate_zero_iff (basisVectors A T)
    (basis_determinant_nonzero A T hcap) P.val.rep i).mp hz
  have hne : basisPoints A T (next i) ≠ basisPoints A T (previous i) :=
    fun h => next_ne_previous i (basisPoints_injective A T h)
  apply not_collinear_white_two_black (configuration A) P (basisPoints A T (next i))
    (basisPoints A T (previous i)) hne
  exact (triple_cycle P.val.rep (basisVectors A T (next i)) (basisVectors A T (previous i))).trans hraw

theorem blackFrame_white_coordinates_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (P : A.W) :
    ∀ i, blackFrame A T hcap P.val.rep i ≠ 0 := by
  intro i
  rw [blackFrame_apply]
  fin_cases i
  · exact mul_ne_zero (xScale_nonzero A T hcap) (base_white_coordinates_nonzero A T hcap P 0)
  · exact mul_ne_zero (yScale_nonzero A T hcap) (base_white_coordinates_nonzero A T hcap P 1)
  · exact base_white_coordinates_nonzero A T hcap P 2

theorem normalized_white_coordinates_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) (P : A.W) :
    ∀ i, blackFrame A T hcap (A.E P) i ≠ 0 := by
  obtain ⟨a, ha, hE⟩ := A.representatives P
  intro i
  rw [hE, map_smul]
  exact mul_ne_zero ha (blackFrame_white_coordinates_nonzero A T hcap P i)

end Cylinder.BMMFourTupleFrame

end
