module

public import Cylinder.BMMFourTupleCoordinateAlgebra

/-! Five actual secant sum equations determine the two additional
white vectors and the fourth black parameter. -/

@[expose] public section

namespace Cylinder.BMMFourSecantCoordinateAlgebra

variable {K : Type*} [Field K]

theorem extra_white_coordinates (a c b : K) (ha : a ≠ 0) (htwo : (2 : K) ≠ 0)
    (X Y : Fin 3 → K) (t25 t83 t58 t45 t81 : K)
    (h25 : ![-a, -a, c - 2 * a] + X = t25 • ![0, 1, 0])
    (h83 : Y + ![a, -a, -c] = t83 • ![0, 1, 0])
    (h58 : X + Y = t58 • ![0, 1, 1])
    (h45 : ![-a, a, -c] + X = t45 • ![0, 1, b])
    (h81 : Y + ![a, a, c] = t81 • ![0, 1, b]) :
    X = ![a, 3 * a - 4 * c, 2 * a - c] ∧
      Y = ![-a, 4 * c - a, c] ∧ b = (2 : K)⁻¹ := by
  have hx0 := congrFun h25 0
  have hx2 := congrFun h25 2
  have hy0 := congrFun h83 0
  have hy2 := congrFun h83 2
  have hxy1 := congrFun h58 1
  have hxy2 := congrFun h58 2
  have h45y := congrFun h45 1
  have h45z := congrFun h45 2
  have h81y := congrFun h81 1
  have h81z := congrFun h81 2
  change -a + X 0 = t25 * 0 at hx0
  change c - 2 * a + X 2 = t25 * 0 at hx2
  change Y 0 + a = t83 * 0 at hy0
  change Y 2 + -c = t83 * 0 at hy2
  change X 1 + Y 1 = t58 * 1 at hxy1
  change X 2 + Y 2 = t58 * 1 at hxy2
  change a + X 1 = t45 * 1 at h45y
  change -c + X 2 = t45 * b at h45z
  change Y 1 + a = t81 * 1 at h81y
  change Y 2 + c = t81 * b at h81z
  have hx0' : X 0 = a := by linear_combination hx0
  have hx2' : X 2 = 2 * a - c := by linear_combination hx2
  have hy0' : Y 0 = -a := by linear_combination hy0
  have hy2' : Y 2 = c := by linear_combination hy2
  have hy1' : Y 1 = 2 * a - X 1 := by
    linear_combination hxy1 - hxy2 + hx2' + hy2'
  have hleft : b * (a + X 1) = 2 * a - 2 * c := by
    linear_combination b * h45y - h45z + hx2'
  have hright : b * (3 * a - X 1) = 2 * c := by
    linear_combination b * h81y - h81z - b * hy1' + hy2'
  have hfactor : (2 * a) * (2 * b - 1) = 0 := by
    linear_combination hleft + hright
  have hb2 : 2 * b = 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero htwo ha))
  have hx1' : X 1 = 3 * a - 4 * c := by
    linear_combination 2 * hleft - (a + X 1) * hb2
  refine ⟨?_, ?_, ?_⟩
  · ext j
    fin_cases j
    · exact hx0'
    · exact hx1'
    · exact hx2'
  · ext j
    fin_cases j
    · exact hy0'
    · change Y 1 = 4 * c - a
      linear_combination hy1' - hx1'
    · exact hy2'
  · calc
      b = (2 : K)⁻¹ * (2 * b) := by rw [← mul_assoc, inv_mul_cancel₀ htwo, one_mul]
      _ = (2 : K)⁻¹ := by rw [hb2, mul_one]

end Cylinder.BMMFourSecantCoordinateAlgebra

end
