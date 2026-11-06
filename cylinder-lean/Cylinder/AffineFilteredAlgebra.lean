module

public import Cylinder.AffineIdealLeading

/-! The genuine finite quotient by two nonhomogeneous binary equations
with relatively prime top homogeneous forms. Every class is reduced to
degree at most `e+t-2` by actual polynomial corrections. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineFilteredAlgebra

open MvPolynomial Module
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionSocle
open Cylinder.AffineIdealReduction Cylinder.AffineIdealLeading Cylinder.LeadingComponents
open scoped Classical

variable {K : Type*} [Field K]

theorem subtract_top_correction (f g P : BinaryRing K) (e t N : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hP : P.totalDegree ≤ N) (hN : e + t - 1 ≤ N) :
    ∃ Q : BinaryRing K, (Q = 0 ∨ Q.totalDegree < N) ∧
      Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P := by
  let fe := homogeneousComponent e f
  let ge := homogeneousComponent t g
  have hfehom : fe.IsHomogeneous e := homogeneousComponent_isHomogeneous e f
  have hgehom : ge.IsHomogeneous t := homogeneousComponent_isHomogeneous t g
  let H : BinaryForms K N := ⟨homogeneousComponent N P, homogeneousComponent_isHomogeneous N P⟩
  have hHI : H ∈ idealPiece fe ge N :=
    homogeneous_high_mem_ideal fe ge e t N he ht hfehom hgehom hfe hge hcop H.val H.property hN
  rw [← gradedGenerator_range fe ge e t N hfehom hgehom] at hHI
  obtain ⟨A, hA⟩ := hHI
  have hAeq : A.1.val * fe + A.2.val * ge = homogeneousComponent N P := congrArg Subtype.val hA
  have hen : e ≤ N := by omega
  have htn : t ≤ N := by omega
  have hAd : A.1.val.totalDegree ≤ N - e := (shiftedForms_homogeneous e N A.1).totalDegree_le
  have hBd : A.2.val.totalDegree ≤ N - t := (shiftedForms_homogeneous t N A.2).totalDegree_le
  have hAb : CoefficientBound A.1.val e N := Or.inr (by omega)
  have hBb : CoefficientBound A.2.val t N := Or.inr (by omega)
  let R := A.1.val * f + A.2.val * g
  have hRI : R ∈ equationsIdeal f g := Ideal.mem_span_pair.mpr ⟨A.1.val, A.2.val, rfl⟩
  have hRd : R.totalDegree ≤ N := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · have h := totalDegree_mul A.1.val f; rw [hf] at h; omega
    · have h := totalDegree_mul A.2.val g; rw [hg] at h; omega
  have hRtop : homogeneousComponent N R = homogeneousComponent N P := by
    dsimp [R]
    rw [map_add, component_product_of_bound A.1.val f e N hf hAb,
      component_product_of_bound A.2.val g t N hg hBb,
      shiftedProjection_val e N hen, shiftedProjection_val t N htn,
      homogeneousComponent_eq_self (shiftedForms_homogeneous e N A.1),
      homogeneousComponent_eq_self (shiftedForms_homogeneous t N A.2)]
    exact hAeq
  have hQd : (P - R).totalDegree ≤ N := (totalDegree_sub _ _).trans (max_le hP hRd)
  have hQtop : homogeneousComponent N (P - R) = 0 := by rw [map_sub, hRtop, sub_self]
  refine ⟨P - R, eq_zero_or_totalDegree_lt_of_component_zero _ N hQd hQtop, ?_⟩
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hRI, sub_zero]

private theorem low_representative_aux (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) (N : ℕ) :
    ∀ P : BinaryRing K, P.totalDegree ≤ N →
      ∃ Q : BinaryRing K, Q.totalDegree ≤ e + t - 2 ∧
        Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro P hP
    by_cases hsmall : P.totalDegree ≤ e + t - 2
    · exact ⟨P, hsmall, rfl⟩
    · have hlarge : e + t - 1 ≤ N := by omega
      obtain ⟨Q, hQd, hQP⟩ := subtract_top_correction f g P e t N he ht hf hg hfe hge hcop hP hlarge
      rcases hQd with rfl | hQd
      · exact ⟨0, by simp, hQP⟩
      · obtain ⟨R, hR, hRQ⟩ := ih Q.totalDegree hQd Q (le_refl _)
        exact ⟨R, hR, hRQ.trans hQP⟩

/-- The degree cutoff for the actual nonhomogeneous quotient, deduced from
the relatively prime highest homogeneous equations. -/
theorem exists_low_degree_representative (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) (P : BinaryRing K) :
    ∃ Q : BinaryRing K, Q.totalDegree ≤ e + t - 2 ∧
      Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P :=
  low_representative_aux f g e t he ht hf hg hfe hge hcop P.totalDegree P (le_refl _)

def filteredQuotientMap (f g : BinaryRing K) (N : ℕ) :
    restrictTotalDegree (Fin 2) K N →ₗ[K] QuotientRing f g :=
  (Ideal.Quotient.mkₐ K (equationsIdeal f g)).toLinearMap.comp (restrictTotalDegree (Fin 2) K N).subtype

theorem filteredQuotientMap_surjective (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    Function.Surjective (filteredQuotientMap f g (e + t - 2)) := by
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨Q, hQ, hQP⟩ := exists_low_degree_representative f g e t he ht hf hg hfe hge hcop P
  exact ⟨⟨Q, (mem_restrictTotalDegree _ _ _).mpr hQ⟩, hQP⟩

theorem quotient_finiteDimensional (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    FiniteDimensional K (QuotientRing f g) :=
  FiniteDimensional.of_surjective (filteredQuotientMap f g (e + t - 2))
    (filteredQuotientMap_surjective f g e t he ht hf hg hfe hge hcop)

#print axioms exists_low_degree_representative
#print axioms quotient_finiteDimensional

end Cylinder.AffineFilteredAlgebra

end
