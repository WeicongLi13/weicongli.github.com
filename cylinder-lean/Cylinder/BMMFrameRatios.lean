module

public import Cylinder.BMMTriangleFrame

/-! The genuine coordinate-ratio identity along a line through a vertex
of the white triangle. These are explicit vector identities. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFrameRatios

open Cylinder.PlaneCrossProduct Cylinder.BMMTriangleFrame

variable {K : Type*} [Field K]

def next (i : Fin 3) : Fin 3 := ![1, 2, 0] i

def previous (i : Fin 3) : Fin 3 := ![2, 0, 1] i

@[simp] theorem next_previous (i : Fin 3) : next (previous i) = i := by fin_cases i <;> rfl

@[simp] theorem previous_next (i : Fin 3) : previous (next i) = i := by fin_cases i <;> rfl

@[simp] theorem next_next (i : Fin 3) : next (next i) = previous i := by fin_cases i <;> rfl

@[simp] theorem previous_previous (i : Fin 3) : previous (previous i) = next i := by
  fin_cases i <;> rfl

theorem next_ne (i : Fin 3) : next i ≠ i := by fin_cases i <;> decide

theorem previous_ne (i : Fin 3) : previous i ≠ i := by fin_cases i <;> decide

theorem next_ne_previous (i : Fin 3) : next i ≠ previous i := by fin_cases i <;> decide

theorem numerators_cyclic (v : Fin 3 → Fin 3 → K) (x : Fin 3 → K) (i : Fin 3) :
    numerators v x i = dot (cross (v (next i)) (v (previous i))) x := by
  fin_cases i <;> rfl

theorem coordinate_zero_iff (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x : Fin 3 → K) (i : Fin 3) :
    coordinates v hd x i = 0 ↔ dot (cross (v (next i)) (v (previous i))) x = 0 := by
  rw [coordinates_apply, numerators_cyclic, mul_eq_zero]
  exact or_iff_right (inv_ne_zero hd)

theorem coordinates_nonzero (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x : Fin 3 → K) (hx : x ≠ 0) : coordinates v hd x ≠ 0 := by
  intro hz
  exact hx ((coordinates v hd).injective (hz.trans (map_zero _).symm))

theorem numerator_minor_identity (v : Fin 3 → Fin 3 → K) (x y : Fin 3 → K) (i : Fin 3) :
    numerators v x (next i) * numerators v y (previous i) -
      numerators v x (previous i) * numerators v y (next i) =
      determinant v * dot (cross (v i) x) y := by
  fin_cases i <;> simp [next, previous, numerators, determinant, dot, cross,
    Fin.sum_univ_succ] <;> ring

theorem coordinates_minor_zero (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x y : Fin 3 → K) (i : Fin 3) (hcol : dot (cross (v i) x) y = 0) :
    coordinates v hd x (next i) * coordinates v hd y (previous i) =
      coordinates v hd x (previous i) * coordinates v hd y (next i) := by
  have hminor := numerator_minor_identity v x y i
  rw [hcol, mul_zero] at hminor
  have hprod := sub_eq_zero.mp hminor
  rw [coordinates_apply, coordinates_apply, coordinates_apply, coordinates_apply]
  calc
    _ = (determinant v)⁻¹ ^ 2 *
      (numerators v x (next i) * numerators v y (previous i)) := by ring
    _ = (determinant v)⁻¹ ^ 2 *
      (numerators v x (previous i) * numerators v y (next i)) := by rw [hprod]
    _ = _ := by ring

theorem collinear_anchor_ratio (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x y : Fin 3 → K) (i : Fin 3) (hcol : dot (cross (v i) x) y = 0)
    (hx : coordinates v hd x (previous i) ≠ 0) (hy : coordinates v hd y (previous i) ≠ 0) :
    coordinates v hd x (next i) / coordinates v hd x (previous i) =
      coordinates v hd y (next i) / coordinates v hd y (previous i) := by
  apply (div_eq_div_iff hx hy).mpr
  simpa only [mul_comm] using coordinates_minor_zero v hd x y i hcol

theorem coordinates_two_zeros (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x : Fin 3 → K) (i : Fin 3) (hi : coordinates v hd x i = 0)
    (hj : coordinates v hd x (next i) = 0) :
    x = coordinates v hd x (previous i) • v (previous i) := by
  apply (coordinates v hd).injective
  rw [map_smul, coordinates_basis]
  funext j
  fin_cases i <;> fin_cases j <;> simp_all [next, previous, Pi.single_apply]

theorem coordinates_two_zeros_previous (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x : Fin 3 → K) (i : Fin 3) (hi : coordinates v hd x i = 0)
    (hj : coordinates v hd x (previous i) = 0) :
    x = coordinates v hd x (next i) • v (next i) := by
  have h := coordinates_two_zeros v hd x (previous i) hj (by simpa only [next_previous] using hi)
  simpa only [previous_previous] using h

end Cylinder.BMMFrameRatios

end
