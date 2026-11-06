module

public import Cylinder.BMMFrameRatios

/-! Coefficients on a genuine projective secant. Two distinct point
representatives are completed to a basis by a coordinate vector. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMVectorSecants

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMTriangleFrame Cylinder.BMMFrameRatios

variable {K : Type*} [Field K]

theorem exists_completion_index (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    ∃ k : Fin 3, cross P.rep Q.rep k ≠ 0 := by
  have hc := cross_ne_zero P.rep Q.rep P.rep_nonzero
    (representatives_not_proportional P Q hPQ)
  by_contra h
  push Not at h
  exact hc (funext h)

def completionIndex (P Q : PlanePoint K) (hPQ : P ≠ Q) : Fin 3 :=
  Classical.choose (exists_completion_index P Q hPQ)

theorem completionIndex_nonzero (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    cross P.rep Q.rep (completionIndex P Q hPQ) ≠ 0 :=
  Classical.choose_spec (exists_completion_index P Q hPQ)

def pairVectors (P Q : PlanePoint K) (hPQ : P ≠ Q) : Fin 3 → Fin 3 → K :=
  ![P.rep, Q.rep, Pi.single (completionIndex P Q hPQ) 1]

theorem pair_determinant_ne_zero (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    determinant (pairVectors P Q hPQ) ≠ 0 := by
  have heq : determinant (pairVectors P Q hPQ) =
      cross P.rep Q.rep (completionIndex P Q hPQ) := by
    simp [determinant, pairVectors, dot, Pi.single_apply]
  rw [heq]
  exact completionIndex_nonzero P Q hPQ

abbrev pairFrame (P Q : PlanePoint K) (hPQ : P ≠ Q) :=
  coordinates (pairVectors P Q hPQ) (pair_determinant_ne_zero P Q hPQ)

theorem pairFrame_left (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    pairFrame P Q hPQ P.rep = (Pi.single 0 1 : Fin 3 → K) := by
  exact coordinates_basis (pairVectors P Q hPQ) (pair_determinant_ne_zero P Q hPQ) 0

theorem pairFrame_right (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    pairFrame P Q hPQ Q.rep = (Pi.single 1 1 : Fin 3 → K) := by
  exact coordinates_basis (pairVectors P Q hPQ) (pair_determinant_ne_zero P Q hPQ) 1

theorem secant_coordinate_zero (P Q R : PlanePoint K) (hPQ : P ≠ Q)
    (hcol : Collinear P Q R) : pairFrame P Q hPQ R.rep 2 = 0 := by
  apply (coordinate_zero_iff (pairVectors P Q hPQ)
    (pair_determinant_ne_zero P Q hPQ) R.rep 2).mpr
  exact hcol

theorem secant_coordinates_nonzero (P Q R : PlanePoint K) (hPQ : P ≠ Q)
    (hPR : P ≠ R) (hQR : Q ≠ R) (hcol : Collinear P Q R) :
    pairFrame P Q hPQ R.rep 0 ≠ 0 ∧ pairFrame P Q hPQ R.rep 1 ≠ 0 := by
  have h2 := secant_coordinate_zero P Q R hPQ hcol
  constructor
  · intro h0
    have hp := coordinates_two_zeros (pairVectors P Q hPQ)
      (pair_determinant_ne_zero P Q hPQ) R.rep 2 h2 h0
    exact representatives_not_proportional Q R hQR _ hp
  · intro h1
    have hp := coordinates_two_zeros_previous (pairVectors P Q hPQ)
      (pair_determinant_ne_zero P Q hPQ) R.rep 2 h2 h1
    exact representatives_not_proportional P R hPR _ hp

theorem exists_secant_representation (P Q R : PlanePoint K) (hPQ : P ≠ Q)
    (hPR : P ≠ R) (hQR : Q ≠ R) (hcol : Collinear P Q R) :
    ∃ b : K, b ≠ 0 ∧ ∃ a : K, a ≠ 0 ∧ R.rep = a • (P.rep + b • Q.rep) := by
  let x := pairFrame P Q hPQ R.rep
  have hx := secant_coordinates_nonzero P Q R hPQ hPR hQR hcol
  refine ⟨x 1 / x 0, div_ne_zero hx.2 hx.1, x 0, hx.1, ?_⟩
  apply (pairFrame P Q hPQ).injective
  rw [map_smul, map_add, map_smul, pairFrame_left, pairFrame_right]
  have h2 := secant_coordinate_zero P Q R hPQ hcol
  funext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, x, h2,
    mul_div_cancel₀, hx.1]

theorem secant_representation_unique (P Q R : PlanePoint K) (hPQ : P ≠ Q)
    (a b a' b' : K) (ha : a ≠ 0)
    (h : R.rep = a • (P.rep + b • Q.rep))
    (h' : R.rep = a' • (P.rep + b' • Q.rep)) : b = b' := by
  have heq := congrArg (pairFrame P Q hPQ) (h.symm.trans h')
  simp only [map_smul, map_add, pairFrame_left, pairFrame_right] at heq
  have h0 : a = a' := by
    simpa [Pi.single_apply, Pi.smul_apply, smul_eq_mul] using congrFun heq 0
  have h1 : a * b = a' * b' := by
    simpa [Pi.single_apply, Pi.smul_apply, smul_eq_mul] using congrFun heq 1
  rw [← h0] at h1
  exact mul_left_cancel₀ ha h1

end Cylinder.BMMVectorSecants

end
