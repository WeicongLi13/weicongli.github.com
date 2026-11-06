module

public import Cylinder.AffineFilteredAlgebra

/-! An actual top homogeneous form vanishes in the associated degree
quotient precisely when the corresponding affine class has a lower-degree
representative. This supplies the kernel of the associated-graded bridge. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineGradedCriterion

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.LeadingComponents
open Cylinder.AffineIdealReduction Cylinder.AffineIdealLeading
open scoped Classical

variable {K : Type*} [Field K]

theorem shiftedProjection_self (e N : ℕ) (A : shiftedForms (K := K) e N) :
    (shiftedProjection (K := K) e N A.val).val = A.val := by
  by_cases he : e ≤ N
  · rw [shiftedProjection_val e N he, homogeneousComponent_eq_self (shiftedForms_homogeneous e N A)]
  · rw [shiftedForms_zero_of_not_le e N A he, map_zero]
    rfl

theorem shifted_coefficient_bound (e N : ℕ) (A : shiftedForms (K := K) e N) :
    CoefficientBound A.val e N := by
  by_cases he : e ≤ N
  · have hd := (shiftedForms_homogeneous e N A).totalDegree_le
    exact Or.inr (by omega)
  · exact Or.inl (shiftedForms_zero_of_not_le e N A he)

theorem product_degree_of_bound (A f : BinaryRing K) (e N : ℕ)
    (hf : f.totalDegree = e) (hA : CoefficientBound A e N) :
    (A * f).totalDegree ≤ N := by
  rcases hA with rfl | hA
  · simp
  · have h := totalDegree_mul A f
    rw [hf] at h
    exact h.trans hA

theorem lower_representative_of_component_mem (f g P : BinaryRing K) (e t N : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t) (hP : P.totalDegree ≤ N)
    (hI : homogeneousComponent N P ∈
      equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g)) :
    ∃ Q : BinaryRing K, (Q = 0 ∨ Q.totalDegree < N) ∧
      Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P := by
  let fe := homogeneousComponent e f
  let ge := homogeneousComponent t g
  have hfehom : fe.IsHomogeneous e := homogeneousComponent_isHomogeneous e f
  have hgehom : ge.IsHomogeneous t := homogeneousComponent_isHomogeneous t g
  let H : BinaryForms K N := ⟨homogeneousComponent N P, homogeneousComponent_isHomogeneous N P⟩
  have hH : H ∈ idealPiece fe ge N := hI
  rw [← gradedGenerator_range fe ge e t N hfehom hgehom] at hH
  obtain ⟨A, hA⟩ := hH
  have hAeq : A.1.val * fe + A.2.val * ge = homogeneousComponent N P := congrArg Subtype.val hA
  let R := A.1.val * f + A.2.val * g
  have hRI : R ∈ equationsIdeal f g := Ideal.mem_span_pair.mpr ⟨A.1.val, A.2.val, rfl⟩
  have hRd : R.totalDegree ≤ N :=
    (totalDegree_add _ _).trans (max_le
      (product_degree_of_bound A.1.val f e N hf (shifted_coefficient_bound e N A.1))
      (product_degree_of_bound A.2.val g t N hg (shifted_coefficient_bound t N A.2)))
  have hRtop : homogeneousComponent N R = homogeneousComponent N P := by
    dsimp [R]
    rw [map_add, component_product_of_bound A.1.val f e N hf (shifted_coefficient_bound e N A.1),
      component_product_of_bound A.2.val g t N hg (shifted_coefficient_bound t N A.2),
      shiftedProjection_self, shiftedProjection_self]
    exact hAeq
  have hQd : (P - R).totalDegree ≤ N := (totalDegree_sub _ _).trans (max_le hP hRd)
  have hQtop : homogeneousComponent N (P - R) = 0 := by rw [map_sub, hRtop, sub_self]
  refine ⟨P - R, eq_zero_or_totalDegree_lt_of_component_zero _ N hQd hQtop, ?_⟩
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hRI, sub_zero]

/-- The actual associated-degree kernel criterion for nonhomogeneous
equations. This is proved from bounded representations and actual top terms. -/
theorem component_mem_iff_lower_representative (f g P : BinaryRing K) (e t N : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hP : P.totalDegree ≤ N) (hN : 0 < N) :
    homogeneousComponent N P ∈ equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) ↔
      ∃ Q : BinaryRing K, Q.totalDegree < N ∧
        Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P := by
  constructor
  · intro hI
    obtain ⟨Q, hQ, hQP⟩ := lower_representative_of_component_mem f g P e t N hf hg hP hI
    exact ⟨Q, hQ.elim (fun h => by rw [h]; simpa using hN) id, hQP⟩
  · rintro ⟨Q, hQ, hQP⟩
    have hPQI : P - Q ∈ equationsIdeal f g := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, ← hQP, sub_self]
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_bounded_representation f g (P - Q) e t hf hg hfe hcop hPQI
    have hPQd : (P - Q).totalDegree ≤ N :=
      (totalDegree_sub _ _).trans (max_le hP (by omega))
    have hAN : CoefficientBound A e N := hA.imp_right (fun h => h.trans hPQd)
    have hBN : CoefficientBound B t N := hB.imp_right (fun h => h.trans hPQd)
    have h := congrArg (homogeneousComponent N) hAB
    rw [map_add, component_product_of_bound A f e N hf hAN,
      component_product_of_bound B g t N hg hBN,
      map_sub, homogeneousComponent_eq_zero _ _ hQ, sub_zero] at h
    exact Ideal.mem_span_pair.mpr ⟨(shiftedProjection e N A).val, (shiftedProjection t N B).val, h⟩

#print axioms lower_representative_of_component_mem
#print axioms component_mem_iff_lower_representative

end Cylinder.AffineGradedCriterion

end
