module

public import Cylinder.ActualRelationCharacter
public import Cylinder.CompleteIntersectionPointBound

/-! Connected numerical characters of actual points on an irreducible curve. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.IrreduciblePointCharacter

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.PlaneNumericalCharacter Cylinder.HilbertCharacterFormulas
open Cylinder.PlaneGap Cylinder.NumericCharacterSequence

variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [Nonempty I]

/-- An actual full-support relation in degree d>=2e excludes every character
gap: the true gap curve would meet the irreducible curve in too many points. -/
theorem connected_character (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F)
    (hzero : ∀ i, eval (v i) F = 0) (hs : InitialDegree v e)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ) (hd : 2 * e ≤ d)
    (hrel : PowerEvaluationRelation.Relation v c d) :
    ∀ j, 0 < j → j < e → numericalCharacter v (j - 1) ≤ numericalCharacter v j + 1 := by
  intro j hj0 hje
  by_contra hn
  have hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1) := by omega
  obtain ⟨G, hG0, hG, hGdeg, _houtside, hlength, _hind⟩ :=
    gap_data v hv hsep e j hs hj0 hje hgap
  have hn_j := (ActualRelationCharacter.character_gap_bounds v hv hsep e hs c hc d hrel).2
    j hj0 hje hgap
  have hanti : Antitone (numericalCharacter v) := character_antitone
  have hhead : j * (e + 1) ≤ ∑ i ∈ Finset.range j, (numericalCharacter v i - i) := by
    calc
      _ = ∑ _i ∈ Finset.range j, (e + 1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j - 1 := by have h := Finset.mem_range.mp hi; omega
        have hn_i := hanti hij
        omega
  have hcop : IsRelPrime F G := by
    apply hirr.isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have hdeg := totalDegree_le_of_dvd_of_isDomain hdiv hG0
    rw [hF.totalDegree hirr.ne_zero, hGdeg] at hdeg
    omega
  have hnonzero : ∀ i : Inside v G, (fun k : Inside v G => v k.val) i ≠ 0 :=
    fun i => hv i.val
  have hdistinct : ProjectivelyDistinct (fun i : Inside v G => v i.val) := by
    intro i k hik a
    exact hsep i.val k.val (fun h => hik (Subtype.ext h)) a
  have hbound := CompleteIntersectionPointBound.cardinal_bound F G e j (by omega) hj0 hF hG
    hirr.ne_zero hcop (fun i : Inside v G => v i.val) hnonzero hdistinct
    (fun i => ⟨hzero i.val, i.property⟩)
  rw [hlength] at hbound
  have hstrict : e * j < j * (e + 1) := by
    simpa only [mul_comm e j] using Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self e) hj0
  omega

end Cylinder.IrreduciblePointCharacter

end
