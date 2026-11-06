module

public import Cylinder.AffineGradedCriterion

/-! Minimal-degree representatives of actual affine quotient classes and
their nonzero highest classes modulo the actual leading ideal. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineMinimalDegree

open MvPolynomial Module
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.AffineGradedCriterion
open scoped Classical

variable {K : Type*} [Field K]

theorem exists_minimal_representative (f g : BinaryRing K) (a : QuotientRing f g) :
    ∃ P : BinaryRing K, Ideal.Quotient.mk (equationsIdeal f g) P = a ∧
      ∀ Q : BinaryRing K, Ideal.Quotient.mk (equationsIdeal f g) Q = a → P.totalDegree ≤ Q.totalDegree := by
  have hN : ∃ N : ℕ, ∃ P : BinaryRing K,
      P.totalDegree = N ∧ Ideal.Quotient.mk (equationsIdeal f g) P = a := by
    obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨P.totalDegree, P, rfl, hP⟩
  obtain ⟨P, hPdeg, hPa⟩ := Nat.find_spec hN
  refine ⟨P, hPa, ?_⟩
  intro Q hQ
  rw [hPdeg]
  exact Nat.find_min' hN ⟨Q, rfl, hQ⟩

theorem exists_minimal_low_representative (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (a : QuotientRing f g) :
    ∃ P : BinaryRing K, Ideal.Quotient.mk (equationsIdeal f g) P = a ∧
      P.totalDegree ≤ e + t - 2 ∧
      ∀ Q : BinaryRing K, Ideal.Quotient.mk (equationsIdeal f g) Q = a → P.totalDegree ≤ Q.totalDegree := by
  obtain ⟨P, hPa, hmin⟩ := exists_minimal_representative f g a
  obtain ⟨R, hRdeg, hRP⟩ := AffineFilteredAlgebra.exists_low_degree_representative
    f g e t he ht hf hg hfe hge hcop P
  exact ⟨P, hPa, (hmin R (hRP.trans hPa)).trans hRdeg, hmin⟩

theorem minimal_top_not_mem (f g P : BinaryRing K) (e t : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hP : Ideal.Quotient.mk (equationsIdeal f g) P ≠ 0)
    (hmin : ∀ Q : BinaryRing K,
      Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P →
        P.totalDegree ≤ Q.totalDegree) :
    homogeneousComponent P.totalDegree P ∉
      equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) := by
  intro htop
  obtain ⟨Q, hQ, hQP⟩ := lower_representative_of_component_mem f g P e t P.totalDegree
    hf hg (le_refl _) htop
  rcases hQ with rfl | hQ
  · exact hP (hQP.symm.trans (map_zero _))
  · have hm := hmin Q hQP
    omega

#print axioms exists_minimal_low_representative
#print axioms minimal_top_not_mem

end Cylinder.AffineMinimalDegree

end
