module

public import Cylinder.LocalCurveInterpolation
public import Cylinder.ActualCharacterBounds
public import Cylinder.EquationScalarDescent

/-! True supports of evaluation relations, and the initial degree forced
by sufficiently many points on an irreducible curve. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentSupport

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.EquationScalarDescent Cylinder.LocalCurveInterpolation

variable {K I : Type*} [Field K] [Fintype I]

def supportIndices (c : I → K) : Finset I := Finset.univ.filter (fun i => c i ≠ 0)

abbrev Support (c : I → K) := {i : I // c i ≠ 0}

theorem support_card_eq (c : I → K) : Fintype.card (Support c) = (supportIndices c).card :=
  Fintype.card_subtype _

theorem relation_sub (v : I → Fin 3 → K) (c w : I → K) (d : ℕ)
    (hc : PowerEvaluationRelation.Relation v c d) (hw : PowerEvaluationRelation.Relation v w d) :
    PowerEvaluationRelation.Relation v (fun i => c i - w i) d := by
  intro F hF
  simpa only [sub_mul, Finset.sum_sub_distrib, hc F hF, hw F hF, sub_self]

theorem relation_after_polynomial_multiplication (v : I → Fin 3 → K)
    (c : I → K) (d a : ℕ) (had : a ≤ d) (Q : PlaneRing K) (hQ : Q.IsHomogeneous a)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    PowerEvaluationRelation.Relation v (fun i => c i * eval (v i) Q) (d - a) := by
  intro H hH
  have hprod : (Q * H).IsHomogeneous d := by
    have h := hQ.mul hH
    rwa [Nat.add_sub_cancel' had] at h
  simpa only [map_mul, mul_assoc] using hrel (Q * H) hprod

theorem relation_on_support (v : I → Fin 3 → K) (c : I → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    PowerEvaluationRelation.Relation (fun i : Support c => v i.val) (fun i => c i.val) d := by
  intro Q hQ
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : I => c i ≠ 0)
    (fun i => c i * eval (v i) Q)
  have hout : (∑ i : {i : I // ¬c i ≠ 0}, c i.val * eval (v i.val) Q) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [not_not.mp i.property, zero_mul]
  rw [hout, add_zero, hrel Q hQ] at hsplit
  exact hsplit

theorem support_representatives_distinct (v : I → Fin 3 → K) (c : I → K)
    (hsep : ProjectivelyDistinct v) : ProjectivelyDistinct (fun i : Support c => v i.val) := by
  intro i j hij a
  exact hsep i.val j.val (fun h => hij (Subtype.ext h)) a

theorem support_eq_zero_of_independent (v : I → Fin 3 → K) (c : I → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation v c d)
    (hind : EvaluationProjection.Independent (fun i : Support c => v i.val) d) : c = 0 := by
  have hzero := CompleteIntersectionSupport.relation_eq_zero_of_independent
    (fun i : Support c => v i.val) (fun i => c i.val) d hind (relation_on_support v c d hrel)
  funext i
  by_cases hi : c i ≠ 0
  · exact congrFun hzero ⟨i, hi⟩
  · exact not_not.mp hi

variable [Infinite K]

theorem initialDegree_of_many_curve_points (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (F : PlaneRing K) (e : ℕ) (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hcard : e * (e - 1) < Fintype.card I) :
    InitialDegree v e := by
  refine ⟨(idealPiece_ne_bot_iff v e).mpr ⟨F, hF, hirr.ne_zero, hzero⟩, ?_⟩
  intro n hn
  by_contra hbot
  obtain ⟨Q, hQ, hQ0, hQzero⟩ := (idealPiece_ne_bot_iff v n).mp hbot
  have hbound := curve_cardinal_bound F Q e n hF hirr hQ hQ0 hn v hv hsep
    (fun i => ⟨hzero i, hQzero i⟩)
  have hle := Nat.mul_le_mul_left e (show n ≤ e - 1 by omega)
  omega

theorem support_character_lower (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (F : PlaneRing K) (e : ℕ) (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (c : I → K) (d : ℕ) (hrel : PowerEvaluationRelation.Relation v c d)
    (hsupport : ∀ i, c i ≠ 0 → eval (v i) F = 0)
    (hcard : e * (e - 1) < (supportIndices c).card) :
    e * (d + 3 - e) ≤ (supportIndices c).card := by
  have hcard' : e * (e - 1) < Fintype.card (Support c) := by
    rwa [support_card_eq]
  letI : Nonempty (Support c) := Fintype.card_pos_iff.mp (by omega)
  have hs := initialDegree_of_many_curve_points (fun i : Support c => v i.val)
    (fun i => hv i.val) (support_representatives_distinct v c hsep) F e hF hirr
    (fun i => hsupport i.val i.property) hcard'
  obtain ⟨_, _, _, htrunc⟩ := ActualCharacterBounds.full_support_character_bounds
    (fun i : Support c => v i.val) (fun i => hv i.val)
    (support_representatives_distinct v c hsep) e hs (fun i => c i.val)
    (fun i => i.property) d (relation_on_support v c d hrel)
  simpa only [support_card_eq] using htrunc e (le_refl e)

end Cylinder.GlobalMomentSupport

end
