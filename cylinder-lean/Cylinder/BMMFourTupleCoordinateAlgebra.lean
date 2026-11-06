module

public import Cylinder.BMMFourTupleBlackGeometry

/-! The coordinate calculation for four white vectors. Its hypotheses
are the ten linear equations supplied by the actual normalized black
secants; the white coordinates themselves are conclusions. -/

@[expose] public section
noncomputable section

namespace Cylinder.BMMFourTupleCoordinateAlgebra

variable {K : Type*} [Field K]

theorem four_white_coordinates (E : Fin 4 → Fin 3 → K) (htwo : (2 : K) ≠ 0)
    (h12x : (E 0 + E 1) 0 = 0) (h12y : (E 0 + E 1) 1 = 0)
    (h34x : (E 2 + E 3) 0 = 0)
    (h13y : (E 0 + E 2) 1 = 0) (h13z : (E 0 + E 2) 2 = 0)
    (h14x : (E 0 + E 3) 0 = 0) (h14z : (E 0 + E 3) 2 = 0)
    (h24y : (E 1 + E 3) 1 = 0) (h24xz : (E 1 + E 3) 0 = (E 1 + E 3) 2)
    (h23yz : (E 1 + E 2) 1 = (E 1 + E 2) 2) :
    ∃ a c : K, E 0 = ![a, a, c] ∧ E 1 = ![-a, -a, c - 2 * a] ∧
      E 2 = ![a, -a, -c] ∧ E 3 = ![-a, a, -c] := by
  simp only [Pi.add_apply] at h12x h12y h34x h13y h13z h14x h14z h24y h24xz h23yz
  have htwodiff : (2 : K) * (E 0 0 - E 0 1) = 0 := by
    linear_combination -h24xz + h23yz + h12x + h14x - h12y - h13y - h14z + h13z
  have hab : E 0 0 = E 0 1 := sub_eq_zero.mp ((mul_eq_zero.mp htwodiff).resolve_left htwo)
  refine ⟨E 0 0, E 0 2, ?_, ?_, ?_, ?_⟩
  · funext j
    fin_cases j
    · rfl
    · exact hab.symm
    · rfl
  · funext j
    fin_cases j
    · change E 1 0 = -E 0 0
      linear_combination h12x
    · change E 1 1 = -E 0 0
      linear_combination h12y + hab
    · change E 1 2 = E 0 2 - 2 * E 0 0
      linear_combination -h24xz + h12x + h14x - h14z
  · funext j
    fin_cases j
    · change E 2 0 = E 0 0
      linear_combination h34x - h14x
    · change E 2 1 = -E 0 0
      linear_combination h13y + hab
    · change E 2 2 = -E 0 2
      linear_combination h13z
  · funext j
    fin_cases j
    · change E 3 0 = -E 0 0
      linear_combination h14x
    · change E 3 1 = E 0 0
      linear_combination h24y - h12y - hab
    · change E 3 2 = -E 0 2
      linear_combination h14z

end Cylinder.BMMFourTupleCoordinateAlgebra

end
