module

public import Cylinder.ProjectiveFieldEmbedding
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-! Explicit actual line coefficients through two projective plane points. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.PlaneCrossProduct

variable {K : Type*} [Field K]

def dot (a v : Fin 3 → K) : K := ∑ i, a i * v i

def cross (v w : Fin 3 → K) : Fin 3 → K :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]

theorem dot_cross_left (v w : Fin 3 → K) : dot (cross v w) v = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

theorem dot_cross_right (v w : Fin 3 → K) : dot (cross v w) w = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

theorem cross_ne_zero (v w : Fin 3 → K) (hv : v ≠ 0)
    (hn : ∀ a : K, w ≠ a • v) : cross v w ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    simpa using not_exists.mp h j
  have h01 : v 0 * w 1 - v 1 * w 0 = 0 := congrFun hz 2
  have h02 : v 0 * w 2 - v 2 * w 0 = 0 := by
    have h : v 2 * w 0 - v 0 * w 2 = 0 := congrFun hz 1
    linear_combination -h
  have h12 : v 1 * w 2 - v 2 * w 1 = 0 := congrFun hz 0
  have hminor (i k : Fin 3) : v i * w k - v k * w i = 0 := by
    fin_cases i <;> fin_cases k
    · ring
    · exact h01
    · exact h02
    · change v 1 * w 0 - v 0 * w 1 = 0
      linear_combination -h01
    · ring
    · exact h12
    · change v 2 * w 0 - v 0 * w 2 = 0
      linear_combination -h02
    · change v 2 * w 1 - v 1 * w 2 = 0
      linear_combination -h12
    · ring
  apply hn (w j / v j)
  funext k
  change w k = (w j / v j) * v k
  apply mul_left_cancel₀ hj
  have hcross := sub_eq_zero.mp (hminor j k)
  calc
    v j * w k = v k * w j := hcross
    _ = v j * ((w j / v j) * v k) := by field_simp

theorem annihilator_minors_zero (a v w : Fin 3 → K) (hv : dot a v = 0) (hw : dot a w = 0)
    (i j : Fin 3) : a i * cross v w j - a j * cross v w i = 0 := by
  have hv' : a 0 * v 0 + a 1 * v 1 + a 2 * v 2 = 0 := by
    simpa [dot, Fin.sum_univ_succ, add_assoc] using hv
  have hw' : a 0 * w 0 + a 1 * w 1 + a 2 * w 2 = 0 := by
    simpa [dot, Fin.sum_univ_succ, add_assoc] using hw
  have h01 : a 0 * cross v w 1 - a 1 * cross v w 0 = 0 := by
    change a 0 * (v 2 * w 0 - v 0 * w 2) - a 1 * (v 1 * w 2 - v 2 * w 1) = 0
    linear_combination v 2 * hw' - w 2 * hv'
  have h02 : a 0 * cross v w 2 - a 2 * cross v w 0 = 0 := by
    change a 0 * (v 0 * w 1 - v 1 * w 0) - a 2 * (v 1 * w 2 - v 2 * w 1) = 0
    linear_combination w 1 * hv' - v 1 * hw'
  have h12 : a 1 * cross v w 2 - a 2 * cross v w 1 = 0 := by
    change a 1 * (v 0 * w 1 - v 1 * w 0) - a 2 * (v 2 * w 0 - v 0 * w 2) = 0
    linear_combination v 0 * hw' - w 0 * hv'
  fin_cases i <;> fin_cases j
  · ring
  · exact h01
  · exact h02
  · change a 1 * cross v w 0 - a 0 * cross v w 1 = 0
    linear_combination -h01
  · ring
  · exact h12
  · change a 2 * cross v w 0 - a 0 * cross v w 2 = 0
    linear_combination -h02
  · change a 2 * cross v w 1 - a 1 * cross v w 2 = 0
    linear_combination -h12
  · ring

/-- A nonzero line equation vanishing at two independent vectors is a genuine
nonzero scalar multiple of their explicit cross-product equation. -/
theorem annihilator_proportional (a v w : Fin 3 → K) (ha : a ≠ 0)
    (hc : cross v w ≠ 0) (hv : dot a v = 0) (hw : dot a w = 0) :
    ∃ u : K, u ≠ 0 ∧ a = u • cross v w := by
  obtain ⟨j, hj⟩ : ∃ j, cross v w j ≠ 0 := by
    by_contra hn
    apply hc
    funext j
    simpa using not_exists.mp hn j
  let u := a j / cross v w j
  have heq : a = u • cross v w := by
    funext k
    change a k = (a j / cross v w j) * cross v w k
    apply mul_right_cancel₀ hj
    have hm := sub_eq_zero.mp (annihilator_minors_zero a v w hv hw k j)
    calc
      a k * cross v w j = a j * cross v w k := hm
      _ = ((a j / cross v w j) * cross v w k) * cross v w j := by field_simp
  refine ⟨u, ?_, heq⟩
  intro hu
  exact ha (by rw [heq, hu, zero_smul])

theorem map_cross {L : Type*} [Field L] (f : K →+* L) (v w : Fin 3 → K) :
    (fun j => f (cross v w j)) = cross (fun j => f (v j)) (fun j => f (w j)) := by
  ext j
  fin_cases j <;> simp [cross]

theorem map_dot {L : Type*} [Field L] (f : K →+* L) (a v : Fin 3 → K) :
    f (dot a v) = dot (fun j => f (a j)) (fun j => f (v j)) := by
  simp [dot]

end Cylinder.PlaneCrossProduct

end
