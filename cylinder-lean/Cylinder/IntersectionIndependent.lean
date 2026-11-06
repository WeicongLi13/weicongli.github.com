module

public import Cylinder.IntersectionProjectivePoints
public import Cylinder.GraphPlaneLine

/-!
# Independence of actual reduced intersection point sets

This is `lem:intersectionindependent`. The graph line is constructed
from the actual relatively prime component forms and nonzero point
representatives. Binary generation and the proved Artin evaluation
formula yield independence in every degree at least `s-2`.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionIndependent

open MvPolynomial Cylinder.HilbertEvaluation
open Cylinder.IntersectionZeroSet Cylinder.IntersectionBinaryGeneration Cylinder.IntersectionArtinBridge
open Cylinder.IntersectionProjectivePoints
open scoped BigOperators Classical

variable {K I J : Type*} [Field K] [Infinite K] [Fintype I] [Fintype J]

theorem independent_intersection_representatives
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (hF0 : ∀ i, F i ≠ 0)
    (hcop : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (v : J → Fin 3 → K) (hv : ∀ j, v j ≠ 0) (hsep : ProjectivelyDistinct v)
    (hJ : ∀ j, OnMultipleComponents F (v j)) (d : ℕ) (hd : (∑ i, e i) - 2 ≤ d) :
    EvaluationProjection.Independent v d := by
  by_cases hI : Nonempty I
  · letI := hI
    obtain ⟨a, b, havoid, hR0, hRcop⟩ :=
      GraphPlaneLine.exists_graph_pairwise_coprime_avoiding F e hhom hF0 hcop v hv
    exact independent_intersections_on_graph F e he hhom v hv hsep hJ a b havoid hR0 hRcop d hd
  · intro w
    refine ⟨0, isHomogeneous_zero _ _ d, ?_⟩
    intro j
    obtain ⟨i, k, hik, hi, hk⟩ := hJ j
    exact False.elim (hI ⟨i⟩)

/-- The original conclusion for a true finite set of projective points.
Nonzero, pairwise distinct representatives follow from projectivization. -/
theorem independent_projective_intersection_points
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (hF0 : ∀ i, F i ≠ 0)
    (hcop : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, OnMultipleComponents F x.val.rep)
    (d : ℕ) (hd : (∑ i, e i) - 2 ≤ d) : EvaluationProjection.Independent (representatives T) d :=
  independent_intersection_representatives F e he hhom hF0 hcop (representatives T)
    (representatives_nonzero T) (representatives_distinct T) hT d hd

theorem projective_intersection_evaluation_surjective
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (hF0 : ∀ i, F i ≠ 0)
    (hcop : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, OnMultipleComponents F x.val.rep)
    (d : ℕ) (hd : (∑ i, e i) - 2 ≤ d) :
    Function.Surjective (evaluationMap (representatives T) d) := by
  intro w
  obtain ⟨P, hP, hvals⟩ := independent_projective_intersection_points F e he hhom hF0 hcop T hT d hd w
  exact ⟨⟨P, hP⟩, funext hvals⟩

#print axioms independent_intersection_representatives
#print axioms independent_projective_intersection_points
#print axioms projective_intersection_evaluation_surjective

end Cylinder.IntersectionIndependent

end
