module

public import Cylinder.IntersectionIndependent
public import Cylinder.PowerEvaluationRelation

/-!
# Independence and relation support on actual complete intersections

The two-component case of the proved intersection theorem gives
`cor:CIindependent`. Testing a relation on the actual interpolating
point indicators gives `cor:support`.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CompleteIntersectionSupport

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.IntersectionZeroSet
open Cylinder.IntersectionProjectivePoints Cylinder.IntersectionIndependent
open scoped BigOperators Classical

variable {K J : Type*} [Field K] [Infinite K] [Fintype J]

theorem independent_complete_intersection_representatives
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (v : J → Fin 3 → K) (hv : ∀ j, v j ≠ 0)
    (hsep : ProjectivelyDistinct v) (hJ : ∀ j, eval (v j) F = 0 ∧ eval (v j) G = 0)
    (d : ℕ) (hd : e + t - 2 ≤ d) : EvaluationProjection.Independent v d := by
  have hpos : ∀ i : Fin 2, 0 < (![e, t] i) := by intro i; fin_cases i <;> assumption
  have hhom : ∀ i : Fin 2, (![F, G] i).IsHomogeneous (![e, t] i) := by
    intro i; fin_cases i <;> assumption
  have hnonzero : ∀ i : Fin 2, ![F, G] i ≠ 0 := by intro i; fin_cases i <;> assumption
  have hpair : Pairwise (fun i j : Fin 2 => IsRelPrime (![F, G] i) (![F, G] j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hcop
    · exact hcop.symm
    · exact False.elim (hij rfl)
  apply independent_intersection_representatives ![F, G] ![e, t] hpos hhom hnonzero hpair v hv hsep
  · intro j
    exact ⟨0, 1, by decide, (hJ j).1, (hJ j).2⟩
  · simpa [Fin.sum_univ_two] using hd

theorem independent_complete_intersection_points
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, eval x.val.rep F = 0 ∧ eval x.val.rep G = 0)
    (d : ℕ) (hd : e + t - 2 ≤ d) : EvaluationProjection.Independent (representatives T) d :=
  independent_complete_intersection_representatives F G e t he ht hF hG hF0 hG0 hcop
    (representatives T) (representatives_nonzero T) (representatives_distinct T) hT d hd

omit [Infinite K] in
theorem relation_eq_zero_of_independent (v : J → Fin 3 → K) (c : J → K) (d : ℕ)
    (hind : EvaluationProjection.Independent v d) (hrel : PowerEvaluationRelation.Relation v c d) :
    c = 0 := by
  funext j
  obtain ⟨P, hP, hval⟩ := hind (Pi.single j 1)
  have hsum := hrel P hP
  simp only [hval] at hsum
  simpa [Pi.single_apply] using hsum

/-- An actual homogeneous evaluation relation supported on the complete intersection is zero. -/
theorem complete_intersection_relation_zero
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, eval x.val.rep F = 0 ∧ eval x.val.rep G = 0)
    (c : T → K) (d : ℕ) (hd : e + t - 2 ≤ d)
    (hrel : PowerEvaluationRelation.Relation (representatives T) c d) : c = 0 :=
  relation_eq_zero_of_independent _ c d
    (independent_complete_intersection_points F G e t he ht hF hG hF0 hG0 hcop T hT d hd) hrel

#print axioms independent_complete_intersection_points
#print axioms complete_intersection_relation_zero

end Cylinder.CompleteIntersectionSupport

end
