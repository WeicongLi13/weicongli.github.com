module

public import Cylinder.BMMFrameRatios
public import Cylinder.BMMBlockerPairs

/-! The actual three side blockers of a white triangle. Coordinate zeros
identify these blockers exactly, using the true white-to-black bijection. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMTriangleBlockers

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMTriangleFrame Cylinder.BMMFrameRatios Cylinder.BMMBlockerPairs

variable {K : Type*} [Field K]

structure Triangle (K : Type*) [Field K] where
  W : Finset (PlanePoint K)
  B : Finset (PlanePoint K)
  arc : LineCap W 2
  disjoint : Disjoint W B
  blocks : BlocksSecants W B
  card : B.card + 1 = W.card
  P : Fin 3 → W
  injective : Function.Injective P

abbrev vectors (T : Triangle K) : Fin 3 → Fin 3 → K := fun i => (T.P i).val.rep

theorem determinant_ne_zero (T : Triangle K) : determinant (vectors T) ≠ 0 :=
  white_frame_determinant_ne_zero T.W T.arc (fun i => (T.P i).val) (fun i => (T.P i).property)
    (fun _ _ h => T.injective (Subtype.ext h))

abbrev frame (T : Triangle K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  coordinates (vectors T) (determinant_ne_zero T)

abbrev blackCoordinates (T : Triangle K) (R : T.B) : Fin 3 → K := frame T R.val.rep

abbrev whiteCoordinates (T : Triangle K) (R : T.W) : Fin 3 → K := frame T R.val.rep

def sideBlocker (T : Triangle K) (i : Fin 3) : T.B :=
  secantBlocker T.W T.B T.arc T.disjoint T.blocks T.card (T.P (next i)) (T.P (previous i))
    (fun h => next_ne_previous i (T.injective h))

theorem side_coordinate_zero (T : Triangle K) (i : Fin 3) :
    blackCoordinates T (sideBlocker T i) i = 0 := by
  apply (coordinate_zero_iff (vectors T) (determinant_ne_zero T) _ i).mpr
  exact secantBlocker_collinear T.W T.B T.arc T.disjoint T.blocks T.card
    (T.P (next i)) (T.P (previous i)) _

theorem black_zero_coordinate_iff_side (T : Triangle K) (R : T.B) (i : Fin 3) :
    blackCoordinates T R i = 0 ↔ R = sideBlocker T i := by
  constructor
  · intro hzero
    have hcol := (coordinate_zero_iff (vectors T) (determinant_ne_zero T) R.val.rep i).mp hzero
    exact (secantBlocker_unique T.W T.B T.arc T.disjoint T.blocks T.card
      (T.P (next i)) (T.P (previous i)) (fun h => next_ne_previous i (T.injective h)) R hcol).symm
  · intro h
    rw [h]
    exact side_coordinate_zero T i

theorem black_two_coordinates_not_zero (T : Triangle K) (R : T.B) (i : Fin 3)
    (hi : blackCoordinates T R i = 0) :
    blackCoordinates T R (next i) ≠ 0 ∧ blackCoordinates T R (previous i) ≠ 0 := by
  constructor
  · intro hj
    have hprop := coordinates_two_zeros (vectors T) (determinant_ne_zero T) R.val.rep i hi hj
    have hPR : (T.P (previous i)).val ≠ R.val := by
      intro h
      exact Finset.disjoint_left.mp T.disjoint (T.P (previous i)).property (h ▸ R.property)
    exact representatives_not_proportional (T.P (previous i)).val R.val hPR
      (blackCoordinates T R (previous i)) hprop
  · intro hj
    have hprop := coordinates_two_zeros_previous (vectors T) (determinant_ne_zero T) R.val.rep i hi hj
    have hPR : (T.P (next i)).val ≠ R.val := by
      intro h
      exact Finset.disjoint_left.mp T.disjoint (T.P (next i)).property (h ▸ R.property)
    exact representatives_not_proportional (T.P (next i)).val R.val hPR
      (blackCoordinates T R (next i)) hprop

theorem sideBlocker_injective (T : Triangle K) : Function.Injective (sideBlocker T) := by
  intro i j h
  by_contra hij
  have hzeroi := side_coordinate_zero T i
  have hzeroj := side_coordinate_zero T j
  rw [← h] at hzeroj
  have hnonzero := black_two_coordinates_not_zero T (sideBlocker T i) i hzeroi
  have hcases : j = next i ∨ j = previous i := by
    fin_cases i <;> fin_cases j <;> simp_all [next, previous]
  rcases hcases with hji | hji
  · exact hnonzero.1 (hji ▸ hzeroj)
  · exact hnonzero.2 (hji ▸ hzeroj)

def offTriangleWhites (T : Triangle K) : Finset T.W := Finset.univ.filter (fun R => ∀ i, R ≠ T.P i)

def offTriangleBlacks (T : Triangle K) : Finset T.B := Finset.univ.filter (fun R => ∀ i, R ≠ sideBlocker T i)

theorem offTriangle_white_coordinates_nonzero (T : Triangle K) (R : T.W)
    (hR : R ∈ offTriangleWhites T) : ∀ i, whiteCoordinates T R i ≠ 0 :=
  white_off_triangle_coordinates_nonzero T.W T.arc (fun i => (T.P i).val)
    (fun i => (T.P i).property) (fun _ _ h => T.injective (Subtype.ext h)) R.val R.property
    (fun i h => (Finset.mem_filter.mp hR).2 i (Subtype.ext h))

theorem offTriangle_black_coordinates_nonzero (T : Triangle K) (R : T.B)
    (hR : R ∈ offTriangleBlacks T) : ∀ i, blackCoordinates T R i ≠ 0 := by
  intro i hzero
  exact (Finset.mem_filter.mp hR).2 i ((black_zero_coordinate_iff_side T R i).mp hzero)

end Cylinder.BMMTriangleBlockers

end
