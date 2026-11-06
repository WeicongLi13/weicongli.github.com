module

public import Cylinder.LinearEvaluationTransport
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.LinearCombination

/-! A genuine homogeneous quadric through the centre has only a constant
and a linear term in the ray parameter. Two distinct zeros on every ray
then give a nonzero homogeneous equation on the actual directions. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.QuadricRayAlgebra

open MvPolynomial

variable {K I : Type*} [Field K]

theorem nested_degree_le (Q : MvPolynomial (Fin 4) K) (d : ℕ) (hQ : Q.IsHomogeneous d) :
    (finSuccEquiv K 3 Q).natDegree ≤ d := by
  rw [natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree Q 0).trans hQ.totalDegree_le

theorem nested_top_coefficient (Q : MvPolynomial (Fin 4) K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) :
    (finSuccEquiv K 3 Q).coeff d = C (eval (Fin.cons 1 0) Q) := by
  have htop : ((finSuccEquiv K 3 Q).coeff d).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero (hQ.finSuccEquiv_coeff_isHomogeneous d 0 (by omega)).totalDegree_le
  have hc := totalDegree_eq_zero_iff_eq_C.mp htop
  have aux : ∀ i ∈ Finset.range d, constantCoeff ((finSuccEquiv K 3 Q).coeff i) = 0 := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    apply (hQ.finSuccEquiv_coeff_isHomogeneous i (d - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  have hdeg : (finSuccEquiv K 3 Q).natDegree < d + 1 := Nat.lt_succ_of_le (nested_degree_le Q d hQ)
  have heval : eval (Fin.cons 1 0) Q = constantCoeff ((finSuccEquiv K 3 Q).coeff d) := by
    simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
      eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  rw [hc]
  exact congrArg C heval.symm

theorem split_quadric (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2)
    (hcentre : eval (Fin.cons 1 0) Q = 0) :
    ∃ f A : MvPolynomial (Fin 3) K,
      f.IsHomogeneous 1 ∧ A.IsHomogeneous 2 ∧
      finSuccEquiv K 3 Q = Polynomial.C A + Polynomial.C f * Polynomial.X := by
  let f := (finSuccEquiv K 3 Q).coeff 1
  let A := (finSuccEquiv K 3 Q).coeff 0
  refine ⟨f, A, hQ.finSuccEquiv_coeff_isHomogeneous 1 1 (by decide),
    hQ.finSuccEquiv_coeff_isHomogeneous 0 2 (by decide), ?_⟩
  have htwo : (finSuccEquiv K 3 Q).coeff 2 = 0 := by
    rw [nested_top_coefficient Q 2 hQ, hcentre, C_0]
  have hdeg := nested_degree_le Q 2 hQ
  apply Polynomial.ext
  intro n
  rcases n with _ | _ | n
  · simp [A]
  · simp [f]
  · by_cases hn : n = 0
    · subst n; simpa using htwo
    · have hhigh : (finSuccEquiv K 3 Q).coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      change (finSuccEquiv K 3 Q).coeff (n + 2) = _
      rw [hhigh]
      simp

theorem split_nonzero (Q : MvPolynomial (Fin 4) K) (hQ0 : Q ≠ 0)
    (f A : MvPolynomial (Fin 3) K)
    (hsplit : finSuccEquiv K 3 Q = Polynomial.C A + Polynomial.C f * Polynomial.X) :
    f ≠ 0 ∨ A ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ0
  apply (finSuccEquiv K 3).injective
  simp [hsplit, h.1, h.2]

theorem split_evaluation (Q : MvPolynomial (Fin 4) K) (f A : MvPolynomial (Fin 3) K)
    (hsplit : finSuccEquiv K 3 Q = Polynomial.C A + Polynomial.C f * Polynomial.X)
    (v : Fin 3 → K) (t : K) :
    eval (Fin.cons t v) Q = eval v A + eval v f * t := by
  rw [eval_eq_eval_mv_eval', hsplit]
  simp

theorem two_times_force_coefficients_zero (Q : MvPolynomial (Fin 4) K)
    (f A : MvPolynomial (Fin 3) K)
    (hsplit : finSuccEquiv K 3 Q = Polynomial.C A + Polynomial.C f * Polynomial.X)
    (v : Fin 3 → K) (t u : K) (htu : t ≠ u)
    (ht : eval (Fin.cons t v) Q = 0) (hu : eval (Fin.cons u v) Q = 0) :
    eval v f = 0 ∧ eval v A = 0 := by
  rw [split_evaluation Q f A hsplit] at ht hu
  have hmul : eval v f * (t - u) = 0 := by linear_combination ht - hu
  have hf : eval v f = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr htu)
  exact ⟨hf, by simpa [hf] using ht⟩

theorem equation_from_two_points_per_ray (Q : MvPolynomial (Fin 4) K)
    (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0) (hcentre : eval (Fin.cons 1 0) Q = 0)
    (v : I → Fin 3 → K) (t u : I → K) (htu : ∀ i, t i ≠ u i)
    (ht : ∀ i, eval (Fin.cons (t i) (v i)) Q = 0)
    (hu : ∀ i, eval (Fin.cons (u i) (v i)) Q = 0) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ ∃ F : MvPolynomial (Fin 3) K,
      F.IsHomogeneous d ∧ F ≠ 0 ∧ ∀ i, eval (v i) F = 0 := by
  obtain ⟨f, A, hf, hA, hsplit⟩ := split_quadric Q hQ hcentre
  have hzero : ∀ i, eval (v i) f = 0 ∧ eval (v i) A = 0 :=
    fun i => two_times_force_coefficients_zero Q f A hsplit (v i) (t i) (u i) (htu i) (ht i) (hu i)
  rcases split_nonzero Q hQ0 f A hsplit with hf0 | hA0
  · exact ⟨1, Or.inl rfl, f, hf, hf0, fun i => (hzero i).1⟩
  · exact ⟨2, Or.inr rfl, A, hA, hA0, fun i => (hzero i).2⟩

end Cylinder.QuadricRayAlgebra

end
