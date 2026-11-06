module

public import Cylinder.CompleteIntersectionSupport
public import Cylinder.IntegerRepresentativeRelations

/-! The intersection independence bound in every integer degree.
In a negative allowed degree, two positive-degree components cannot meet
the degree-sum bound, so the point index type is empty. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.IntersectionIntegerIndependent

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.IntersectionZeroSet
open Cylinder.IntersectionIndependent Cylinder.IntersectionProjectivePoints
open Cylinder.IntegerRepresentativeRelations Cylinder.PlaneRelationSpaces

variable {K I J : Type*} [Field K] [Infinite K] [Fintype I] [Fintype J]

theorem index_empty_of_negative_degree
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (v : J → Fin 3 → K) (hJ : ∀ j, OnMultipleComponents F (v j))
    (d : ℤ) (hd : ((∑ i, e i : ℕ) : ℤ) - 2 ≤ d) (hneg : d < 0) :
    IsEmpty J := by
  refine ⟨fun j => ?_⟩
  obtain ⟨i, k, hik, _, _⟩ := hJ j
  have hpair : e i + e k ≤ ∑ a, e a := by
    simpa [Finset.sum_pair hik] using
      (Finset.sum_le_sum_of_subset (Finset.subset_univ ({i, k} : Finset I)) :
        ∑ a ∈ ({i, k} : Finset I), e a ≤ ∑ a ∈ Finset.univ, e a)
  have hi := he i
  have hk := he k
  omega

theorem integer_relations_eq_bot
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (hF0 : ∀ i, F i ≠ 0)
    (hcop : Pairwise (fun i k => IsRelPrime (F i) (F k)))
    (v : J → Fin 3 → K) (hv : ∀ j, v j ≠ 0) (hsep : ProjectivelyDistinct v)
    (hJ : ∀ j, OnMultipleComponents F (v j))
    (d : ℤ) (hd : ((∑ i, e i : ℕ) : ℤ) - 2 ≤ d) :
    integerRelations v d = ⊥ := by
  by_cases hd0 : 0 ≤ d
  · have hnat : (∑ i, e i) - 2 ≤ d.toNat := by omega
    have hind := independent_intersection_representatives F e he hhom hF0 hcop
      v hv hsep hJ d.toNat hnat
    ext c
    simp only [integerRelations, if_pos hd0, Submodule.mem_bot]
    constructor
    · intro hc
      exact Cylinder.CompleteIntersectionSupport.relation_eq_zero_of_independent
        v c d.toNat hind ((mem_relationSpace v d.toNat c).mp hc)
    · intro hc
      rw [hc]
      exact Submodule.zero_mem _
  · letI := index_empty_of_negative_degree F e he v hJ d hd (by omega)
    ext c
    have hc : c = 0 := funext fun j => isEmptyElim j
    simp [hc]

/-- The manuscript's actual reduced projective point set, including all
integer degrees `d ≥ s - 2`, has no nonzero evaluation relations. -/
theorem projective_intersection_integer_relations_eq_bot
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (hF0 : ∀ i, F i ≠ 0)
    (hcop : Pairwise (fun i k => IsRelPrime (F i) (F k)))
    (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, OnMultipleComponents F x.val.rep)
    (d : ℤ) (hd : ((∑ i, e i : ℕ) : ℤ) - 2 ≤ d) :
    integerRelations (representatives T) d = ⊥ :=
  integer_relations_eq_bot F e he hhom hF0 hcop (representatives T)
    (representatives_nonzero T) (representatives_distinct T) hT d hd

end Cylinder.IntersectionIntegerIndependent

end
