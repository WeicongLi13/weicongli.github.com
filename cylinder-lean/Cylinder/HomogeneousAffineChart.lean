module

public import Cylinder.PlaneHomogenization
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Highest-degree affine terms are the actual homogeneous restriction to the chart line. -/

@[expose] public section
noncomputable section

namespace Cylinder.HomogeneousAffineChart

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open scoped Classical BigOperators

variable {K : Type*} [Field K]

def chartAt (a : K) : HomogeneousPlanePolynomial (K := K) →ₐ[K] PlanePolynomial (K := K) :=
  MvPolynomial.aeval (fun i => i.elim (C a) X)

@[simp] theorem chartAt_C (a c : K) : chartAt a (C c) = C c := by simp [chartAt]
@[simp] theorem chartAt_X_none (a : K) : chartAt a (X none) = C a := by simp [chartAt]
@[simp] theorem chartAt_X_some (a : K) (i : Fin 2) : chartAt a (X (some i)) = X i := by simp [chartAt]

theorem chartAt_one (Q : HomogeneousPlanePolynomial (K := K)) : chartAt 1 Q = dehomogenize Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => cases i <;> simp [hF]

theorem chartAt_eq_nested_eval (a : K) (Q : HomogeneousPlanePolynomial (K := K)) :
    chartAt a Q = Polynomial.eval (C a) (optionEquivLeft K (Fin 2) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => cases i <;> simp [hF]

theorem chartAt_zero (Q : HomogeneousPlanePolynomial (K := K)) :
    chartAt 0 Q = (optionEquivLeft K (Fin 2) Q).coeff 0 := by
  rw [chartAt_eq_nested_eval]
  simpa only [C_0] using (Polynomial.coeff_zero_eq_eval_zero (optionEquivLeft K (Fin 2) Q)).symm

theorem chartAt_one_sum (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) :
    chartAt 1 Q = ∑ i ∈ Finset.range (n + 1), (optionEquivLeft K (Fin 2) Q).coeff i := by
  rw [chartAt_eq_nested_eval]
  have hdeg : (optionEquivLeft K (Fin 2) Q).natDegree < n + 1 := by
    rw [natDegree_optionEquivLeft]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree Q none).trans hQ.totalDegree_le)
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp

theorem top_component_chartAt (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) : homogeneousComponent n (chartAt 1 Q) = chartAt 0 Q := by
  let p := optionEquivLeft K (Fin 2) Q
  have hp : ((optionEquivLeft K (Fin 2)).symm p).IsHomogeneous n := by
    simpa only [p, AlgEquiv.symm_apply_apply] using hQ
  rw [chartAt_one_sum n Q hQ, map_sum]
  calc
    _ = homogeneousComponent n (p.coeff 0) := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        have hci := hp.coeff_isHomogeneous_of_optionEquivLeft_symm i (n - i) (by omega)
        rw [homogeneousComponent_of_mem hci, ite_eq_right]
        omega
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
    _ = p.coeff 0 := homogeneousComponent_eq_self
      (hp.coeff_isHomogeneous_of_optionEquivLeft_symm 0 n (by omega))
    _ = chartAt 0 Q := (chartAt_zero Q).symm

theorem chartAt_zero_homogeneous (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) : (chartAt 0 Q).IsHomogeneous n := by
  rw [← top_component_chartAt n Q hQ]
  exact homogeneousComponent_isHomogeneous n _

theorem chartAt_one_totalDegree (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hzero : chartAt 0 Q ≠ 0) : (chartAt 1 Q).totalDegree = n := by
  have hle : (chartAt 1 Q).totalDegree ≤ n := by
    rw [chartAt_one]
    exact (PlaneHomogenization.dehomogenize_totalDegree_le Q).trans hQ.totalDegree_le
  by_contra hne
  have hlt : (chartAt 1 Q).totalDegree < n := lt_of_le_of_ne hle hne
  have hz := homogeneousComponent_eq_zero n (chartAt 1 Q) hlt
  rw [top_component_chartAt n Q hQ] at hz
  exact hzero hz

theorem eval_chartAt (a : K) (u : Fin 2 → K) (Q : HomogeneousPlanePolynomial (K := K)) :
    eval u (chartAt a Q) = eval (fun i => i.elim a u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => cases i <;> simp [hF]

theorem component_chartAt_one (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (k : ℕ) (hk : k ≤ n) :
    homogeneousComponent (n - k) (chartAt 1 Q) = (optionEquivLeft K (Fin 2) Q).coeff k := by
  let p := optionEquivLeft K (Fin 2) Q
  have hp : ((optionEquivLeft K (Fin 2)).symm p).IsHomogeneous n := by
    simpa only [p, AlgEquiv.symm_apply_apply] using hQ
  rw [chartAt_one_sum n Q hQ, map_sum]
  calc
    _ = homogeneousComponent (n - k) (p.coeff k) := by
      apply Finset.sum_eq_single k
      · intro i hi hik
        have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        have hci := hp.coeff_isHomogeneous_of_optionEquivLeft_symm i (n - i) (by omega)
        rw [homogeneousComponent_of_mem hci, ite_eq_right]
        omega
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (by omega)))
    _ = p.coeff k := homogeneousComponent_eq_self
      (hp.coeff_isHomogeneous_of_optionEquivLeft_symm k (n - k) (by omega))

/-- This homogeneous chart is injective over every field, including finite fields. -/
theorem chartAt_one_zero_of_homogeneous (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hz : chartAt 1 Q = 0) : Q = 0 := by
  have hdeg : (optionEquivLeft K (Fin 2) Q).natDegree ≤ n := by
    rw [natDegree_optionEquivLeft]
    exact (degreeOf_le_totalDegree Q none).trans hQ.totalDegree_le
  apply (optionEquivLeft K (Fin 2)).injective
  rw [map_zero]
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_zero]
  by_cases hi : i ≤ n
  · rw [← component_chartAt_one n Q hQ i hi, hz, map_zero]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem chartAt_one_injective_on_homogeneous (n : ℕ)
    (Q R : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n) (hR : R.IsHomogeneous n)
    (heq : chartAt 1 Q = chartAt 1 R) : Q = R := by
  apply sub_eq_zero.mp
  apply chartAt_one_zero_of_homogeneous n (Q - R) (hQ.sub hR)
  rw [map_sub, heq, sub_self]

theorem dehomogenize_injective_on_homogeneous (n : ℕ)
    (Q R : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n) (hR : R.IsHomogeneous n)
    (heq : dehomogenize Q = dehomogenize R) : Q = R := by
  apply chartAt_one_injective_on_homogeneous n Q R hQ hR
  rwa [chartAt_one, chartAt_one]

theorem homogenize_dehomogenize (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) : PlaneHomogenization.homogenize n (dehomogenize Q) = Q := by
  apply dehomogenize_injective_on_homogeneous n _ Q
    (PlaneHomogenization.homogenize_homogeneous n _
      ((PlaneHomogenization.dehomogenize_totalDegree_le Q).trans hQ.totalDegree_le)) hQ
  exact PlaneHomogenization.dehomogenize_homogenize n _

end Cylinder.HomogeneousAffineChart

end
