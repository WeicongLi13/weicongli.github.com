module

public import Cylinder.ConicLineCoordinates
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! An actual quadratic over an algebraically closed field has two
roots counted with multiplicity. This gives a literal factorization of
the corresponding homogeneous binary quadratic. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicBinaryRoots
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport

variable {K : Type*} [Field K]

theorem homogeneous_positive_not_isUnit (F : PlaneRing K) (d : ℕ)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (hF0 : F ≠ 0) : ¬IsUnit F := by
  intro hu
  have hdiv : F ∣ (1 : PlaneRing K) := hu.dvd
  have hle := totalDegree_le_of_dvd_of_isDomain hdiv (one_ne_zero : (1 : PlaneRing K) ≠ 0)
  rw [hF.totalDegree hF0] at hle
  simp only [totalDegree_one] at hle
  omega

theorem coordinate_line_not_isUnit (i j : Fin 3) (hij : i ≠ j) (r : K) :
    ¬IsUnit (X i - C r * X j : PlaneRing K) := by
  apply homogeneous_positive_not_isUnit _ 1
    ((isHomogeneous_X K i).sub (isHomogeneous_C_mul_X r j)) (by decide)
  intro hz
  have h := congrArg (eval (Pi.single i 1)) hz
  simp only [map_sub, map_mul, eval_C, eval_X, Pi.single_apply,
    ite_eq_right (Ne.symm hij), mul_zero, sub_zero, map_zero] at h
  exact one_ne_zero h

theorem exists_quadratic_roots [IsAlgClosed K] (a b c : K) (ha : a ≠ 0) :
    ∃ r s : K, b = -a * (r + s) ∧ c = a * r * s := by
  let P : Polynomial K := Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  have hd : P.degree ≠ 0 := by
    intro hz
    have hcoeff : P.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_degree_lt (by rw [hz]; norm_num)
    have htwo : P.coeff 2 = a := by simp [P]
    exact ha (htwo.symm.trans hcoeff)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hd
  have hroot : a * r ^ 2 + b * r + c = 0 := by
    simpa [P, Polynomial.IsRoot] using hr
  let s := -b / a - r
  have hb : b = -a * (r + s) := by
    dsimp only [s]
    field_simp [ha]
    ring
  refine ⟨r, s, hb, ?_⟩
  rw [hb] at hroot
  linear_combination hroot

theorem homogeneous_binary_factorization [IsAlgClosed K] (a b c : K) (ha : a ≠ 0)
    (i j : Fin 3) :
    ∃ r s : K, (C a * X i ^ 2 + C b * X i * X j + C c * X j ^ 2 : PlaneRing K) =
      C a * (X i - C r * X j) * (X i - C s * X j) := by
  obtain ⟨r, s, hb, hc⟩ := exists_quadratic_roots a b c ha
  refine ⟨r, s, ?_⟩
  rw [hb, hc]
  simp only [map_mul, map_neg, map_add]
  ring

theorem quadratic_in_two_coordinates_not_irreducible [IsAlgClosed K]
    (a b c : K) (ha : a ≠ 0) (i j : Fin 3) (hij : i ≠ j) :
    ¬Irreducible (C a * X i ^ 2 + C b * X i * X j + C c * X j ^ 2 : PlaneRing K) := by
  intro hirr
  obtain ⟨r, s, heq⟩ := homogeneous_binary_factorization a b c ha i j
  have hunit := hirr.isUnit_or_isUnit heq
  rcases hunit with hleft | hright
  · exact coordinate_line_not_isUnit i j hij r (isUnit_of_mul_isUnit_right hleft)
  · exact coordinate_line_not_isUnit i j hij s hright

end Cylinder.ConicBinaryRoots
end
