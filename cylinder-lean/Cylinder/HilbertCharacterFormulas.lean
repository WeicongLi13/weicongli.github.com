module

public import Cylinder.HilbertEvaluation
public import Cylinder.NumericCharacterSequence

/-! Numerical-character formulas for the actual homogeneous evaluation Hilbert
function, conditional on its initial growth and binary Artin monotonicity.
The defect here is cardinality minus evaluation rank; its identification with
ideal-sheaf cohomology is a separate mathematical step. -/

@[expose] public section

noncomputable section

namespace Cylinder.HilbertCharacterFormulas

open Finset
open Cylinder.HilbertEvaluation Cylinder.NumericCharacterSequence

variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

def differences (v : I → Fin 3 → K) : ℕ → ℕ := firstDifference (hilbert v)

def numericalCharacter (v : I → Fin 3 → K) (i : ℕ) : ℕ :=
  character (differences v) (Fintype.card I) i

omit [Nonempty I] in
theorem length_formula (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hshape : Shape (differences v) s (Fintype.card I)) :
    Fintype.card I = ∑ i ∈ range s, (numericalCharacter v i - i) := by
  have h := length_of_firstDifference (hilbert v) (hilbert_monotone v hv) hshape
  rw [hilbert_eq_card_of_card_sub_one_le v hv hsep _ (le_refl _)] at h
  exact h

omit [Nonempty I] in
theorem defect_formula (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hshape : Shape (differences v) s (Fintype.card I)) (d : ℕ) :
    Fintype.card I - hilbert v d = ∑ i ∈ range s,
      ((numericalCharacter v i - (d + 1)) - (i - (d + 1))) := by
  exact defect_of_firstDifference (hilbert v) (hilbert_monotone v hv) hshape
    (Fintype.card I) (fun w hw => hilbert_eq_card_of_card_sub_one_le v hv hsep w hw) d

theorem defect_positive_iff (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hshape : Shape (differences v) s (Fintype.card I)) (d : ℕ) :
    0 < Fintype.card I - hilbert v d ↔ d + 1 < numericalCharacter v 0 := by
  have htail := tail_of_firstDifference (hilbert v) (hilbert_monotone v hv)
    (Fintype.card_pos) (fun w hw => hilbert_eq_card_of_card_sub_one_le v hv hsep w hw) d
  rw [← htail]
  exact tail_positive_iff hshape d

theorem last_positive_defect (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (s : ℕ)
    (hshape : Shape (differences v) s (Fintype.card I))
    (hlarge : 2 ≤ numericalCharacter v 0) :
    0 < Fintype.card I - hilbert v (numericalCharacter v 0 - 2) ∧
      ∀ d, numericalCharacter v 0 - 1 ≤ d → Fintype.card I - hilbert v d = 0 := by
  constructor
  · rw [defect_positive_iff v hv hsep s hshape]
    omega
  · intro d hd
    have hzero : ¬ 0 < Fintype.card I - hilbert v d := by
      rw [defect_positive_iff v hv hsep s hshape]
      omega
    omega

end Cylinder.HilbertCharacterFormulas

end
