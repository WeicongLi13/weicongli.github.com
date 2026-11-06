module

public import Cylinder.PowerRelationScalarExtension
public import Cylinder.ProductFrobenius

/-! The last coefficient-comparison step of `prop:product`, for the actual
white dual points. The Frobenius power identity and its nonzero coefficients
remain explicit inputs until the residue construction supplies them. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProductEvaluationRelation

open MvPolynomial Finset Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance

variable (p : ℕ) [Fact p.Prime]

def coefficientVector (H : DualPoint p) : Vector p := fun j => H.rep (Pi.single j 1)

theorem coefficientVector_ne_zero (H : DualPoint p) : coefficientVector p H ≠ 0 := by
  intro h
  apply H.rep_nonzero
  apply LinearMap.ext
  intro x
  rw [functional_expansion p H.rep x]
  have hz : ∀ j, H.rep (Pi.single j 1) = 0 := fun j => congrFun h j
  simp [hz, ProjectiveGeometry.pairing]

theorem powerSum_white_forms (S : Finset (Geometry.Point p))
    (c : whitePoints p S → ZMod p) (d : ℕ) :
    PowerEvaluationRelation.powerSum (fun e : whitePoints p S => coefficientVector p e.val) c d =
      ∑ e : whitePoints p S, C (c e) * ProductFrobenius.planeForm p e.val ^ d := rfl

theorem full_support_relation_of_frobenius_identity (S : Finset (Geometry.Point p))
    (c : whitePoints p S → ZMod p) (hc : ∀ e, c e ≠ 0)
    (hidentity : (∑ e : whitePoints p S,
      C (c e) * ProductFrobenius.planeForm p e.val ^ (p - 2)) = 0) :
    (∀ e, c e ≠ 0) ∧ PowerEvaluationRelation.Relation
      (fun e : whitePoints p S => coefficientVector p e.val) c (p - 2) := by
  refine ⟨hc, PowerEvaluationRelation.relation_of_powerSum_eq_zero p _ c (p - 2) ?_ ?_⟩
  · have hp := (Fact.out : p.Prime).two_le
    omega
  · rw [powerSum_white_forms]
    exact hidentity

variable {K : Type*} [Field K] [CharP K p]

/-- The canonical embedding of the prime field into the field used for plane curves. -/
def primeEmbedding : ZMod p →+* K := ZMod.castHom (dvd_refl p) K

/-- The relation holds for all forms over the extension field, not just for
forms with prime-field coefficients. Nonzero coefficients remain nonzero. -/
theorem full_support_relation_over_field (S : Finset (Geometry.Point p))
    (c : whitePoints p S → ZMod p) (hc : ∀ e, c e ≠ 0)
    (hidentity : (∑ e : whitePoints p S,
      C (c e) * ProductFrobenius.planeForm p e.val ^ (p - 2)) = 0) :
    (∀ e, primeEmbedding p (K := K) (c e) ≠ 0) ∧
      PowerEvaluationRelation.Relation
        (fun e : whitePoints p S => fun j => primeEmbedding p (K := K) (coefficientVector p e.val j))
        (fun e => primeEmbedding p (K := K) (c e)) (p - 2) := by
  refine ⟨PowerRelationScalarExtension.coefficients_nonzero (primeEmbedding p) c hc, ?_⟩
  apply PowerRelationScalarExtension.relation_of_mapped_power_identity p (primeEmbedding p)
    (fun e : whitePoints p S => coefficientVector p e.val) c (p - 2)
  · have hp := (Fact.out : p.Prime).two_le
    omega
  · rw [powerSum_white_forms]
    exact hidentity

end Cylinder.ProductEvaluationRelation

end
