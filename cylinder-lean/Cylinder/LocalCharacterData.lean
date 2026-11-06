module

public import Cylinder.LocalCharacterPlateau
public import Cylinder.ActualCharacterBounds
public import Cylinder.PlaneRelationSpaces

/-! The local numerical bounds and three relation dimensions are derived
from actual projective evaluation and its actual numerical character. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalCharacterData

open Module Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.HilbertCharacterFormulas Cylinder.ActualCharacterBounds
open Cylinder.ComponentCharacterNumeric Cylinder.LocalCharacterPlateau
open Cylinder.PlaneRelationSpaces Cylinder.NumericalIdealFormula
open Cylinder.NumericCharacterSequence
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

theorem actual_beta_bounds (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (e d m : ℕ) (hs : InitialDegree v e)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (hrel : PowerEvaluationRelation.Relation v u d)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hconn : ∀ i, 0 < i → i < e → numericalCharacter v (i - 1) ≤ numericalCharacter v i + 1)
    (hplateau : increment (numericalCharacter v) d (3 * m + 3) = m) :
    m ≤ increment (numericalCharacter v) d (e - 1) ∧
      increment (numericalCharacter v) d (e - 1) ≤ e - 2 * m - 4 ∧
      numericalCharacter v (e - 1) = (d + 3 - e) + increment (numericalCharacter v) d (e - 1) ∧
      increment (numericalCharacter v) d (e - 1) + 2 * m + 2 ≤ e - 2 := by
  have hlower : ∀ i < e, d + 2 - i ≤ numericalCharacter v i := by
    intro i hi
    exact (le_max_right e (d + 2 - i)).trans
      ((full_support_character_bounds v hv hsep e hs u hu d hrel).1 i hi)
  exact beta_bounds (numericalCharacter v) e d m hm hsmall hd character_antitone hlower hconn hplateau

/-- Actual relation dimensions satisfy the exact three-term plateau
formula used for the residual Hilbert first differences. -/
theorem actual_relation_dimensions (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (e d m : ℕ) (hs : InitialDegree v e)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (hrel : PowerEvaluationRelation.Relation v u d)
    (hm : 0 < m) (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (hconn : ∀ i, 0 < i → i < e → numericalCharacter v (i - 1) ≤ numericalCharacter v i + 1)
    (hplateau : ∀ r < 4, increment (numericalCharacter v) d (3 * m + r) = m)
    (q : ℕ) (hq0 : 2 * m ≤ q) (hq1 : q ≤ 2 * m + 2) :
    finrank K (relationSpace v (d - q)) +
      (∑ i ∈ Finset.range (3 * m), (m - increment (numericalCharacter v) d i)) = triangular (q + m + 1) := by
  rw [relationSpace_character_formula v hv hsep e hs]
  have hlower : ∀ i < e, d + 2 - i ≤ numericalCharacter v i := by
    intro i hi
    exact (le_max_right e (d + 2 - i)).trans
      ((full_support_character_bounds v hv hsep e hs u hu d hrel).1 i hi)
  exact local_defect_sums (numericalCharacter v) e d m hm hsmall hd character_antitone hlower hconn hplateau q hq0 hq1

#print axioms actual_beta_bounds
#print axioms actual_relation_dimensions

end Cylinder.LocalCharacterData

end
