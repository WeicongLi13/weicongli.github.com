module

public import Cylinder.HilbertEvaluation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

/-! Actual first derivatives and nonzero tangent directions at projective points. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.JetEvaluation

open MvPolynomial

variable {K : Type*} [Field K]

abbrev PlaneRing := MvPolynomial (Fin 3) K

def directional (w : Fin 3 → K) : Derivation K (PlaneRing (K := K)) (PlaneRing (K := K)) :=
  ∑ i : Fin 3, (C (w i) : PlaneRing (K := K)) • pderiv (R := K) i

@[simp] theorem directional_C (w : Fin 3 → K) (a : K) : directional w (C a) = 0 := by
  simp [directional]

@[simp] theorem directional_X (w : Fin 3 → K) (j : Fin 3) : directional w (X j) = C (w j) := by
  simp [directional, pderiv_X, Pi.single_apply, smul_eq_mul]

theorem directional_mul (w : Fin 3 → K) (F G : PlaneRing (K := K)) :
    directional w (F * G) = F * directional w G + G * directional w F := by
  simpa only [smul_eq_mul] using (directional w).leibniz F G

def Nonradial (v w : Fin 3 → K) : Prop := ∀ a : K, w ≠ a • v

/-- A true homogeneous linear form separates a nonzero tangent direction
from the radial direction, with its derivative normalized to one. -/
theorem exists_linear_tangent (v w : Fin 3 → K) (hv : v ≠ 0) (hw : Nonradial v w) :
    ∃ L : PlaneRing (K := K), L.IsHomogeneous 1 ∧
      eval v L = 0 ∧ eval v (directional w L) = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    apply hv
    funext j
    simpa using not_exists.mp hn j
  obtain ⟨k, hk⟩ : ∃ k, v j * w k - v k * w j ≠ 0 := by
    by_contra hn
    apply hw (w j / v j)
    funext k
    change w k = (w j / v j) * v k
    have hcross := sub_eq_zero.mp (not_ne_iff.mp (not_exists.mp hn k))
    apply (mul_left_cancel₀ hj)
    calc
      v j * w k = v k * w j := hcross
      _ = v j * ((w j / v j) * v k) := by
        field_simp
  let a := v j * w k - v k * w j
  let L : PlaneRing (K := K) := C a⁻¹ * (C (v j) * X k - C (v k) * X j)
  refine ⟨L, ((isHomogeneous_C_mul_X (v j) k).sub
    (isHomogeneous_C_mul_X (v k) j)).C_mul a⁻¹, ?_, ?_⟩
  · simp [L, mul_comm]
  · simp only [L, directional_mul, directional_C, directional_X,
      map_sub, map_mul, eval_C, mul_zero, add_zero]
    change a⁻¹ * (v j * w k - v k * w j) = 1
    exact inv_mul_cancel₀ hk

theorem square_jet_zero (v w : Fin 3 → K) (F : PlaneRing (K := K)) (hF : eval v F = 0) :
    eval v (F ^ 2) = 0 ∧ eval v (directional w (F ^ 2)) = 0 := by
  constructor
  · simp [hF]
  · simp only [pow_two, directional_mul, map_add, map_mul, hF, zero_mul, add_zero]

def evaluationMap {I : Type*} (v w : I → Fin 3 → K) (d : ℕ) :
    HilbertEvaluation.Forms K d →ₗ[K] (I → Fin 2 → K) where
  toFun F i := ![eval (v i) F.val, eval (v i) (directional (w i) F.val)]
  map_add' F G := by
    ext i j
    fin_cases j <;> simp
  map_smul' a F := by
    ext i j
    fin_cases j <;> simp [smul_eq_mul]

end Cylinder.JetEvaluation

end
