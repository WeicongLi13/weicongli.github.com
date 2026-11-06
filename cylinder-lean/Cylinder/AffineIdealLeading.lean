module

public import Cylinder.AffineIdealReduction

/-! Actual bounded ideal representations and equality of the real leading
ideal with the ideal of the two highest homogeneous equations. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineIdealLeading

open MvPolynomial Module
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.AffineIdealReduction
open scoped Classical

variable {K : Type*} [Field K]

private theorem bounded_representation_aux (f g P : BinaryRing K) (e t : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) (N : ℕ) :
    ∀ A B : BinaryRing K, A * f + B * g = P → CoefficientBound A e N → CoefficientBound B t N →
      ∃ A' B' : BinaryRing K, A' * f + B' * g = P ∧
        CoefficientBound A' e P.totalDegree ∧ CoefficientBound B' t P.totalDegree := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro A B hP hA hB
    by_cases hN : N ≤ P.totalDegree
    · exact ⟨A, B, hP, hA.imp_right (fun h => h.trans hN), hB.imp_right (fun h => h.trans hN)⟩
    · obtain ⟨A', B', hP', hA', hB'⟩ := lower_weighted_representation f g P A B e t N
        hf hg hfe hcop hP (by omega) hA hB
      apply ih (N - 1) (by omega) A' B' hP'
      · exact hA'.imp_right (fun h => by omega)
      · exact hB'.imp_right (fun h => by omega)

theorem exists_bounded_representation (f g P : BinaryRing K) (e t : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hP : P ∈ equationsIdeal f g) :
    ∃ A B : BinaryRing K, A * f + B * g = P ∧
      CoefficientBound A e P.totalDegree ∧ CoefficientBound B t P.totalDegree := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  exact bounded_representation_aux f g P e t hf hg hfe hcop
    (max (A.totalDegree + e) (B.totalDegree + t)) A B hAB
      (Or.inr (le_max_left _ _)) (Or.inr (le_max_right _ _))

theorem top_component_mem_leading_ideal (f g P : BinaryRing K) (e t : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hP : P ∈ equationsIdeal f g) :
    homogeneousComponent P.totalDegree P ∈
      equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_bounded_representation f g P e t hf hg hfe hcop hP
  have h := congrArg (homogeneousComponent P.totalDegree) hAB
  rw [map_add, component_product_of_bound A f e P.totalDegree hf hA,
    component_product_of_bound B g t P.totalDegree hg hB] at h
  exact Ideal.mem_span_pair.mpr ⟨(shiftedProjection e P.totalDegree A).val,
    (shiftedProjection t P.totalDegree B).val, h⟩

def leadingIdeal (J : Ideal (BinaryRing K)) : Ideal (BinaryRing K) :=
  Ideal.span (Set.range fun P : J => homogeneousComponent P.val.totalDegree P.val)

/-- The actual leading ideal equality; no associated-graded equality is
introduced as an assumption. -/
theorem leadingIdeal_eq (f g : BinaryRing K) (e t : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    leadingIdeal (equationsIdeal f g) =
      equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨P, rfl⟩
    exact top_component_mem_leading_ideal f g P.val e t hf hg hfe hcop P.property
  · apply Ideal.span_le.mpr
    intro P hP
    rcases hP with rfl | hP
    · apply Ideal.subset_span
      refine ⟨⟨f, Ideal.subset_span (Set.mem_insert f {g})⟩, ?_⟩
      change homogeneousComponent f.totalDegree f = homogeneousComponent e f
      rw [hf]
    · have hPG := Set.mem_singleton_iff.mp hP
      subst P
      apply Ideal.subset_span
      refine ⟨⟨g, Ideal.subset_span (Set.mem_insert_of_mem f (Set.mem_singleton g))⟩, ?_⟩
      change homogeneousComponent g.totalDegree g = homogeneousComponent t g
      rw [hg]

#print axioms exists_bounded_representation
#print axioms leadingIdeal_eq

end Cylinder.AffineIdealLeading

end

