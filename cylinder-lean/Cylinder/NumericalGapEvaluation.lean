module

public import Cylinder.NumericalCharacterGap
public import Cylinder.ActualIdealCharacter

/-! The gap formulas for the actual homogeneous evaluation Hilbert function.
Its sequence shape is derived from the actual initial degree. -/

@[expose] public section
noncomputable section

namespace Cylinder.NumericalGapEvaluation

open Module Finset
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.HilbertCharacterFormulas Cylinder.NumericCharacterSequence
open Cylinder.NumericalIdealFormula Cylinder.PlaneBinaryReduction
open Cylinder.NumericalCharacterGap

variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

theorem actual_gap_plateau (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (s j : ℕ)
    (hs : InitialDegree v s) (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1)) :
    s ≤ numericalCharacter v j ∧
      differences v (numericalCharacter v j) = j ∧
      differences v (numericalCharacter v j + 1) = j :=
  gap_plateau (derivationShape v hv hsep s hs) hj0 hjs hgap

theorem defect_at_gap (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (s j : ℕ)
    (hs : InitialDegree v s) (hjs : j < s) :
    Fintype.card I - hilbert v (numericalCharacter v j - 1) =
      ∑ i ∈ range s, (numericalCharacter v i - numericalCharacter v j) := by
  have hshape := derivationShape v hv hsep s hs
  rw [HilbertCharacterFormulas.defect_formula v hv hsep s hshape]
  exact gap_defect_sum hshape hjs

/-- The length forced onto the degree-j component is expressed using the
actual Hilbert defect, with no independent Hilbert-shape hypothesis. -/
theorem head_length_from_defect (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (s j : ℕ)
    (hs : InitialDegree v s) (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1)) :
    triangular (numericalCharacter v j) - triangular (numericalCharacter v j - j) +
      (Fintype.card I - hilbert v (numericalCharacter v j - 1)) =
        ∑ i ∈ range j, (numericalCharacter v i - i) := by
  rw [defect_at_gap v hv hsep s j hs hjs]
  exact gap_head_length (derivationShape v hv hsep s hs) hj0 hjs hgap

#print axioms actual_gap_plateau
#print axioms defect_at_gap
#print axioms head_length_from_defect

end Cylinder.NumericalGapEvaluation

end
