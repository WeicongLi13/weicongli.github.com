module

public import Cylinder.JetInterpolation

/-! First-jet ideals and a genuine graded quotient dimension bound. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.JetIdeal

open MvPolynomial Module Cylinder.JetEvaluation Cylinder.HilbertEvaluation

variable {K I : Type*} [Field K]

def firstJetIdeal (v w : I → Fin 3 → K) : Ideal (MvPolynomial (Fin 3) K) where
  carrier := {F | ∀ i, eval (v i) F = 0 ∧ eval (v i) (directional (w i) F) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG i
    simp only [map_add, (hF i).1, (hF i).2, (hG i).1, (hG i).2, add_zero, and_self]
  smul_mem' := by
    intro A F hF i
    simp only [smul_eq_mul, directional_mul, map_add, map_mul, (hF i).1, (hF i).2,
      mul_zero, zero_mul, add_zero, and_self]

theorem span_pair_le_firstJetIdeal (v w : I → Fin 3 → K) (F G : MvPolynomial (Fin 3) K)
    (hF : ∀ i, eval (v i) F = 0 ∧ eval (v i) (directional (w i) F) = 0)
    (hG : ∀ i, eval (v i) G = 0 ∧ eval (v i) (directional (w i) G) = 0) :
    Ideal.span {F, G} ≤ firstJetIdeal v w := by
  apply Ideal.span_le.mpr
  intro H hH
  rcases Set.mem_insert_iff.mp hH with rfl | hH
  · exact hF
  · rw [Set.mem_singleton_iff] at hH
    subst H
    exact hG

def idealPiece (J : Ideal (MvPolynomial (Fin 3) K)) (d : ℕ) : Submodule K (Forms K d) :=
  (J.restrictScalars K).comap (Forms K d).subtype

def quotientFormsMap (J : Ideal (MvPolynomial (Fin 3) K)) (d : ℕ) :
    Forms K d →ₗ[K] (MvPolynomial (Fin 3) K ⧸ J) :=
  (Ideal.Quotient.mkₐ K J).toLinearMap.comp (Forms K d).subtype

theorem quotientFormsMap_kernel (J : Ideal (MvPolynomial (Fin 3) K)) (d : ℕ) :
    LinearMap.ker (quotientFormsMap J d) = idealPiece J d := by
  ext F
  simp [quotientFormsMap, idealPiece, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem graded_quotient_finrank_eq_range (J : Ideal (MvPolynomial (Fin 3) K)) (d : ℕ) :
    finrank K (Forms K d ⧸ idealPiece J d) =
      finrank K (LinearMap.range (quotientFormsMap J d)) := by
  rw [← quotientFormsMap_kernel J d]
  exact (quotientFormsMap J d).quotKerEquivRange.finrank_eq

theorem idealPiece_le_jet_kernel (v w : I → Fin 3 → K)
    (J : Ideal (MvPolynomial (Fin 3) K)) (hJ : J ≤ firstJetIdeal v w) (d : ℕ) :
    idealPiece J d ≤ LinearMap.ker (JetEvaluation.evaluationMap v w d) := by
  intro F hF
  have h : ∀ i, eval (v i) F.val = 0 ∧
      eval (v i) (directional (w i) F.val) = 0 := hJ hF
  apply LinearMap.mem_ker.mpr
  ext i j
  fin_cases j
  · exact (h i).1
  · exact (h i).2

variable [Fintype I] [Infinite K]

/-- Each actual value and tangent derivative imposes an independent condition;
the quotient bound follows from a constructed surjective map. -/
theorem two_card_le_graded_quotient (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (hw : ∀ i, Nonradial (v i) (w i))
    (J : Ideal (MvPolynomial (Fin 3) K)) (hJ : J ≤ firstJetIdeal v w)
    (d : ℕ) (hd : 2 * Fintype.card I - 1 ≤ d) :
    2 * Fintype.card I ≤ finrank K (Forms K d ⧸ idealPiece J d) := by
  let f := JetEvaluation.evaluationMap v w d
  have hker := idealPiece_le_jet_kernel v w J hJ d
  let g := (idealPiece J d).liftQ f hker
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨F, hF⟩ := JetInterpolation.first_jet_evaluation_surjective_of_le v w hv hsep hw d hd y
    exact ⟨Submodule.Quotient.mk F, hF⟩
  have h := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa only [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Module.finrank_self,
    one_mul] using h

end Cylinder.JetIdeal

end
