module

public import Cylinder.PlaneBinaryReduction
public import Cylinder.HilbertCharacterFormulas
public import Cylinder.NumericalIdealFormula

/-! Ideal-piece dimensions in terms of the numerical character. -/

@[expose] public section
noncomputable section

namespace Cylinder.ActualIdealCharacter

open Module Finset
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.HilbertCharacterFormulas Cylinder.NumericCharacterSequence
open Cylinder.NumericalIdealFormula Cylinder.PlaneBinaryReduction

variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
theorem forms_dimension (d : ℕ) : finrank K (Forms K d) = triangular (d + 1) := by
  induction d with
  | zero => rw [forms_finrank_zero]; rfl
  | succ d ih =>
      rw [forms_rank_succ, ih]
      simp only [triangular]
      omega

/-- The formula for the actual degree-d vanishing subspace. The binary Hilbert
shape is explicit until its derivation from initial degree is connected. -/
theorem ideal_dimension_from_shape [Infinite K] (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (s : ℕ)
    (hshape : Shape (differences v) s (Fintype.card I)) (d : ℕ) (hs : s ≤ d + 1) :
    finrank K (idealPiece v d) = triangular (d + 1 - s) +
      ∑ i ∈ range s, (d + 1 - numericalCharacter v i) := by
  have hr := ideal_piece_dimension v d
  rw [← idealPiece_eq_kernel, forms_dimension] at hr
  have hc := graded_dimension_identity (hilbert v) (hilbert_monotone v hv) hshape d hs
  change triangular (d + 1) = hilbert v d +
    (triangular (d + 1 - s) + ∑ i ∈ range s, (d + 1 - numericalCharacter v i)) at hc
  omega

/-- The manuscript's ideal-dimension formula, derived from the genuine initial
degree. A negative residual degree has dimension zero, represented by triangular 0. -/
theorem ideal_dimension [Infinite K] [Nonempty I] (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hinitial : InitialDegree v s) (d : ℕ) (hs : s ≤ d + 1) :
    finrank K (idealPiece v d) = triangular (d + 1 - s) +
      ∑ i ∈ range s, (d + 1 - numericalCharacter v i) :=
  ideal_dimension_from_shape v hv s (derivationShape v hv hsep s hinitial) d hs

/-- Length and numerical defect formulas with no assumed Hilbert-sequence shape. -/
theorem character_formulas [Infinite K] [Nonempty I] (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hinitial : InitialDegree v s) :
    (∀ i < s, s ≤ numericalCharacter v i) ∧
    Antitone (numericalCharacter v) ∧
    Fintype.card I = ∑ i ∈ range s, (numericalCharacter v i - i) ∧
    ∀ d, Fintype.card I - hilbert v d = ∑ i ∈ range s,
      ((numericalCharacter v i - (d + 1)) - (i - (d + 1))) := by
  have hshape := derivationShape v hv hsep s hinitial
  refine ⟨fun i hi => character_ge_initial_size hshape hi,
    character_antitone, HilbertCharacterFormulas.length_formula v hv hsep s hshape,
    fun d => HilbertCharacterFormulas.defect_formula v hv hsep s hshape d⟩

end Cylinder.ActualIdealCharacter

end
