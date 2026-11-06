module

public import Cylinder.JetEvaluation

/-! Homogeneous interpolation of values and actual first derivatives. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.JetInterpolation

open MvPolynomial Cylinder.JetEvaluation Cylinder.HilbertEvaluation

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem exists_single_jet (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hw : ∀ i, Nonradial (v i) (w i))
    (i : I) (a b : K) :
    ∃ P : MvPolynomial (Fin 3) K, P.IsHomogeneous (2 * Fintype.card I - 1) ∧
      (∀ j, eval (v j) P = if j = i then a else 0) ∧
      ∀ j, eval (v j) (directional (w j) P) = if j = i then b else 0 := by
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding v hv
  obtain ⟨G, hG, hGi, hGj⟩ := exists_point_separator v hsep L hL hLv i
  let H : MvPolynomial (Fin 3) K := C (eval (v i) G)⁻¹ * G
  have hH : H.IsHomogeneous (Fintype.card I - 1) := hG.C_mul _
  have hHi : eval (v i) H = 1 := by simp [H, hGi]
  have hHj (j : I) (hji : j ≠ i) : eval (v j) H = 0 := by simp [H, hGj j hji]
  obtain ⟨T, hT, hTi, hDiT⟩ := exists_linear_tangent (v i) (w i) (hv i) (hw i)
  let A := L * H ^ 2
  let B := T * H ^ 2
  have hdegree : 1 + (Fintype.card I - 1) * 2 = 2 * Fintype.card I - 1 := by
    have hp : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  have hA : A.IsHomogeneous (2 * Fintype.card I - 1) := by
    simpa only [hdegree] using hL.mul (hH.pow 2)
  have hB : B.IsHomogeneous (2 * Fintype.card I - 1) := by
    simpa only [hdegree] using hT.mul (hH.pow 2)
  have hAi : eval (v i) A = eval (v i) L := by simp [A, hHi]
  have hBi : eval (v i) B = 0 := by simp [B, hTi]
  have hDiB : eval (v i) (directional (w i) B) = 1 := by
    simp only [B, directional_mul, map_add, map_mul, hTi, hDiT, map_pow, hHi,
      zero_mul, one_pow, one_mul, zero_add]
  have hother (j : I) (hji : j ≠ i) :
      eval (v j) A = 0 ∧ eval (v j) B = 0 ∧
        eval (v j) (directional (w j) A) = 0 ∧
          eval (v j) (directional (w j) B) = 0 := by
    obtain ⟨hz, hdz⟩ := square_jet_zero (v j) (w j) H (hHj j hji)
    simp only [A, B, directional_mul, map_add, map_mul, hz, hdz, zero_mul,
      mul_zero, add_zero, and_self]
  let c := a / eval (v i) L
  let z := b - c * eval (v i) (directional (w i) A)
  let P := C c * A + C z * B
  refine ⟨P, (hA.C_mul c).add (hB.C_mul z), ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [P, map_add, map_mul, eval_C, hAi, hBi, mul_zero, add_zero, ite_true]
      exact div_mul_cancel₀ _ (hLv i)
    · obtain ⟨hAj, hBj, _⟩ := hother j hji
      simp [P, hAj, hBj, hji]
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [P, map_add, directional_mul, directional_C, map_mul, eval_C,
        mul_zero, add_zero, hDiB, mul_one, ite_true]
      simp [z]
    · obtain ⟨hAj, hBj, hDAj, hDBj⟩ := hother j hji
      simp [P, hDAj, hDBj, hji]

/-- Every prescribed value and tangent derivative is realized by a genuine
homogeneous form in degree `2|D|-1`. -/
theorem first_jet_interpolation (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hw : ∀ i, Nonradial (v i) (w i))
    (a b : I → K) :
    ∃ P : MvPolynomial (Fin 3) K, P.IsHomogeneous (2 * Fintype.card I - 1) ∧
      (∀ i, eval (v i) P = a i) ∧
        ∀ i, eval (v i) (directional (w i) P) = b i := by
  choose P hP hval hder using fun i => exists_single_jet v w hv hsep hw i (a i) (b i)
  refine ⟨∑ i, P i, IsHomogeneous.sum Finset.univ P _ (fun i _ => hP i), ?_, ?_⟩
  · intro j
    simp only [map_sum, hval]
    simp
  · intro j
    simp only [map_sum, hder]
    simp

theorem first_jet_evaluation_surjective (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hw : ∀ i, Nonradial (v i) (w i)) :
    Function.Surjective (JetEvaluation.evaluationMap v w (2 * Fintype.card I - 1)) := by
  intro f
  obtain ⟨P, hP, hval, hder⟩ := first_jet_interpolation v w hv hsep hw
    (fun i => f i 0) (fun i => f i 1)
  refine ⟨⟨P, hP⟩, ?_⟩
  ext i j
  fin_cases j <;> simp [JetEvaluation.evaluationMap, hval, hder]

/-- Multiplication by a constructed avoiding form preserves interpolation
of both value and derivative in every higher degree. -/
theorem first_jet_interpolation_of_le (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hw : ∀ i, Nonradial (v i) (w i))
    (d : ℕ) (hd : 2 * Fintype.card I - 1 ≤ d) (a b : I → K) :
    ∃ P : MvPolynomial (Fin 3) K, P.IsHomogeneous d ∧
      (∀ i, eval (v i) P = a i) ∧
        ∀ i, eval (v i) (directional (w i) P) = b i := by
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding v hv
  let A := L ^ (d - (2 * Fintype.card I - 1))
  have hAi : ∀ i, eval (v i) A ≠ 0 := fun i => by
    simpa only [A, map_pow] using pow_ne_zero _ (hLv i)
  obtain ⟨P, hP, hval, hder⟩ := first_jet_interpolation v w hv hsep hw
    (fun i => a i / eval (v i) A)
    (fun i => (b i - eval (v i) (directional (w i) A) *
      (a i / eval (v i) A)) / eval (v i) A)
  refine ⟨A * P, ?_, ?_, ?_⟩
  · have h := (hL.pow (d - (2 * Fintype.card I - 1))).mul hP
    simpa only [one_mul, Nat.sub_add_cancel hd] using h
  · intro i
    rw [map_mul, hval, mul_div_cancel₀ _ (hAi i)]
  · intro i
    simp only [directional_mul, map_add, map_mul, hval, hder]
    field_simp [hAi i]
    ring

theorem first_jet_evaluation_surjective_of_le (v w : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hw : ∀ i, Nonradial (v i) (w i)) (d : ℕ) (hd : 2 * Fintype.card I - 1 ≤ d) :
    Function.Surjective (JetEvaluation.evaluationMap v w d) := by
  intro f
  obtain ⟨P, hP, hval, hder⟩ := first_jet_interpolation_of_le v w hv hsep hw d hd
    (fun i => f i 0) (fun i => f i 1)
  refine ⟨⟨P, hP⟩, ?_⟩
  ext i j
  fin_cases j <;> simp [JetEvaluation.evaluationMap, hval, hder]

end Cylinder.JetInterpolation

end
