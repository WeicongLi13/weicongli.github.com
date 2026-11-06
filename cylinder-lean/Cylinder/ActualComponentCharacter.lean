module

public import Cylinder.IrreduciblePointCharacter
public import Cylinder.ComponentCharacterNumeric
public import Cylinder.WeightedFormRelations
public import Cylinder.ActualCharacterBounds
public import Cylinder.ActualIdealCharacter

/-! The component-character conclusions for actual irreducible-curve points. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ActualComponentCharacter

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.HilbertCharacterFormulas Cylinder.NumericCharacterSequence
open Cylinder.ComponentCharacterNumeric Cylinder.PlaneRelationSpaces

variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

theorem character_increments (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hs : InitialDegree v e)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ) (hd : 2 * e ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    (∀ j, 0 < j → j < e → numericalCharacter v (j - 1) ≤ numericalCharacter v j + 1) ∧
    (∀ j < e, numericalCharacter v j = (d + 2 - j) + increment (numericalCharacter v) d j) ∧
    (∀ j, j + 1 < e → increment (numericalCharacter v) d j ≤ increment (numericalCharacter v) d (j + 1) ∧
      increment (numericalCharacter v) d (j + 1) ≤ increment (numericalCharacter v) d j + 1) ∧
    (∑ j ∈ Finset.range e, increment (numericalCharacter v) d j) =
      Fintype.card I - e * (d + 3 - e) := by
  have hconn := IrreduciblePointCharacter.connected_character v hv hsep F e hF hirr hzero hs c hc d hd hrel
  have hanti : Antitone (numericalCharacter v) := character_antitone
  obtain ⟨hbound, _hsum, _hmax, _htrunc⟩ :=
    ActualCharacterBounds.full_support_character_bounds v hv hsep e hs c hc d hrel
  have hlower : ∀ j < e, d + 2 - j ≤ numericalCharacter v j :=
    fun j hj => (le_max_right e _).trans (hbound j hj)
  obtain ⟨hexact, hinc⟩ := increment_bounds (numericalCharacter v) e d hd hanti hlower hconn
  have hlength := length_formula v hv hsep e (derivationShape v hv hsep e hs)
  have hsum := length_increment_sum (numericalCharacter v) e d (Fintype.card I) hd hlower hlength
  exact ⟨hconn, hexact, hinc, by omega⟩

theorem small_relation_ranks (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e : ℕ) (he : 4 ≤ e)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hs : InitialDegree v e)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ) (hd : 2 * e ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d)
    (hb3 : increment (numericalCharacter v) d 3 = 0) :
    finrank K (relationSpace v (d - 1)) = 3 ∧ finrank K (relationSpace v (d - 2)) = 6 := by
  have hconn := IrreduciblePointCharacter.connected_character v hv hsep F e hF hirr hzero hs c hc d hd hrel
  have hanti : Antitone (numericalCharacter v) := character_antitone
  obtain ⟨hbound, _hsum, _hmax, _htrunc⟩ :=
    ActualCharacterBounds.full_support_character_bounds v hv hsep e hs c hc d hrel
  have hlower : ∀ j < e, d + 2 - j ≤ numericalCharacter v j :=
    fun j hj => (le_max_right e _).trans (hbound j hj)
  have hsums := small_defect_sums (numericalCharacter v) e d he hd hanti hlower hconn hb3
  have hr1 := relationSpace_character_formula v hv hsep e hs (d - 1)
  have hr2 := relationSpace_character_formula v hv hsep e hs (d - 2)
  rw [show d - 1 + 1 = d by omega] at hr1
  rw [show d - 2 + 1 = d - 1 by omega] at hr2
  exact ⟨hr1.trans hsums.1, hr2.trans hsums.2⟩

/-- When b_3=0, every actual lower-degree relation is multiplication of the
full-support relation by a genuine linear or quadratic plane form. -/
theorem zero_third_forms (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e : ℕ) (he : 4 ≤ e)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hs : InitialDegree v e)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ) (hd : 2 * e ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d)
    (hb3 : increment (numericalCharacter v) d 3 = 0)
    (m1 m2 : I → K)
    (hm1 : PowerEvaluationRelation.Relation v m1 (d - 1))
    (hm2 : PowerEvaluationRelation.Relation v m2 (d - 2)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, m1 i = eval (v i) f * c i) ∧ ∀ i, m2 i = eval (v i) g * c i := by
  have hranks := small_relation_ranks v hv hsep F e he hF hirr hzero hs c hc d hd hrel hb3
  have hdim1 : finrank K (Forms K 1) = finrank K (relationSpace v (d - 1)) := by
    rw [hranks.1, ActualIdealCharacter.forms_dimension]
    rfl
  have hdim2 : finrank K (Forms K 2) = finrank K (relationSpace v (d - 2)) := by
    rw [hranks.2, ActualIdealCharacter.forms_dimension]
    rfl
  obtain ⟨f, hf, hvals1⟩ := WeightedFormRelations.exists_weighted_form v c hc e d 1 hs
    (by omega) (by omega) hrel hdim1 m1 hm1
  obtain ⟨g, hg, hvals2⟩ := WeightedFormRelations.exists_weighted_form v c hc e d 2 hs
    (by omega) (by omega) hrel hdim2 m2 hm2
  exact ⟨f, g, hf, hg, hvals1, hvals2⟩

/-- The common nonzero component weight cancels pointwise. This is the
manuscript's passage from mu_v=H*m_(v+1) to m_2=f*u and m_3=g*u. -/
theorem zero_third_after_common_weight (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e : ℕ) (he : 4 ≤ e)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hs : InitialDegree v e)
    (a c : I → K) (ha : ∀ i, a i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (d : ℕ) (hd : 2 * e ≤ d)
    (hrel : PowerEvaluationRelation.Relation v (fun i => a i * c i) d)
    (hb3 : increment (numericalCharacter v) d 3 = 0) (m1 m2 : I → K)
    (hm1 : PowerEvaluationRelation.Relation v (fun i => a i * m1 i) (d - 1))
    (hm2 : PowerEvaluationRelation.Relation v (fun i => a i * m2 i) (d - 2)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, m1 i = eval (v i) f * c i) ∧ ∀ i, m2 i = eval (v i) g * c i := by
  obtain ⟨f, g, hf, hg, hvals1, hvals2⟩ := zero_third_forms v hv hsep F e he hF hirr hzero hs
    (fun i => a i * c i) (fun i => mul_ne_zero (ha i) (hc i)) d hd hrel hb3
    (fun i => a i * m1 i) (fun i => a i * m2 i) hm1 hm2
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · intro i
    apply mul_left_cancel₀ (ha i)
    calc
      _ = eval (v i) f * (a i * c i) := hvals1 i
      _ = _ := by ring
  · intro i
    apply mul_left_cancel₀ (ha i)
    calc
      _ = eval (v i) g * (a i * c i) := hvals2 i
      _ = _ := by ring

end Cylinder.ActualComponentCharacter

end
