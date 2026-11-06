module

public import Cylinder.ThreeNetConicArithmetic
public import Cylinder.ActualCharacterBounds
public import Cylinder.InitialDegreeExists
public import Cylinder.EquationScalarDescent
public import Cylinder.RationalPlanePointModel

/-! The conic-support step in the primary 3-net theorem. A relation on the
actual 2n point representatives, rather than conic existence, is the input.
The rational conic is obtained by coefficient descent when needed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ThreeNetConicSupport
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.EquationScalarDescent

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem conic_of_full_support_relation (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (n : ℕ)
    (hcard : Fintype.card I = 2 * n) (c : I → K) (hc : ∀ i, c i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation v c (n - 1)) :
    ∃ Q : PlaneRing K, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧ ∀ i, eval (v i) Q = 0 := by
  by_cases hn : n = 0
  · have hzero : Fintype.card I = 0 := by omega
    let _ : IsEmpty I := Fintype.card_eq_zero_iff.mp hzero
    exact ⟨X (0 : Fin 3) ^ 2, isHomogeneous_X_pow (R := K) 0 2,
      pow_ne_zero 2 (X_ne_zero _), fun i => isEmptyElim i⟩
  · let _ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree v
    obtain ⟨_hchar, hbound, _hsharp, htruncated⟩ :=
      ActualCharacterBounds.full_support_character_bounds v hv hsep s hs c hc (n - 1) hrel
    rw [hcard] at hbound htruncated
    have htwo := ThreeNetConicArithmetic.initial_degree_le_two n s hbound htruncated
    obtain ⟨F, hF, hF0, hvan⟩ := (idealPiece_ne_bot_iff v s).mp hs.1
    let Q := X (0 : Fin 3) ^ (2 - s) * F
    refine ⟨Q, ?_, mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) hF0, ?_⟩
    · simpa only [Nat.sub_add_cancel htwo] using
        (isHomogeneous_X_pow (R := K) (0 : Fin 3) (2 - s)).mul hF
    · intro i
      change eval (v i) (X (0 : Fin 3) ^ (2 - s) * F) = 0
      rw [map_mul, hvan i, mul_zero]

/-- The actual base-field point set lies on a base-field conic. The
relation coefficients may lie in an infinite extension field. -/
theorem rational_conic_of_full_support_relation {R : Type*} [Field R] [Algebra R K]
    (D : Finset (RationalPlaneLine.PlanePoint R)) (n : ℕ) (hcard : D.card = 2 * n)
    (c : D → K) (hc : ∀ i, c i ≠ 0)
    (hrel : PowerEvaluationRelation.Relation
      (RationalPlanePointModel.representatives (algebraMap R K) D) c (n - 1)) :
    ∃ Q : PlaneRing R, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧ ∀ P ∈ D, eval P.rep Q = 0 := by
  obtain ⟨Q, hQ, hQ0, hzero⟩ := conic_of_full_support_relation
    (RationalPlanePointModel.representatives (algebraMap R K) D)
    (RationalPlanePointModel.representatives_nonzero _ _)
    (RationalPlanePointModel.representatives_distinct _ _) n
    (by simpa only [Fintype.card_coe] using hcard) c hc hrel
  obtain ⟨F, hF, hF0, hvan⟩ := exists_equation_descent (fun P : D => P.val.rep) 2 Q hQ hQ0 hzero
  exact ⟨F, hF, hF0, fun P hP => hvan ⟨P, hP⟩⟩

end Cylinder.ThreeNetConicSupport
end
