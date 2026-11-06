module

public import Cylinder.FrobeniusAnnihilator

/-! The genuine total-degree filtration on the homogeneous binary quotient
and its complementary orthogonal filtration under the constructed residue
functional. This is the homogeneous algebraic part of filtered duality. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionFiltered

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionSocle Cylinder.CompleteIntersectionAdjoint
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionPerfectPairing
open Cylinder.CompleteIntersectionFrobenius
open scoped Classical BigOperators

variable {K : Type*} [Field K]

local instance : GradedAlgebra (BinaryForms K) := MvPolynomial.gradedAlgebra

theorem component_mul_homogeneous (P Q : BinaryRing K) (d r : ℕ)
    (hQ : Q.IsHomogeneous r) :
    homogeneousComponent (d + r) (P * Q) = homogeneousComponent d P * Q := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem (BinaryForms K)
    (i := d) (j := r) (a := P) (b := Q) hQ
  have hc (R : BinaryRing K) (n : ℕ) :
      (DirectSum.decompose (BinaryForms K) R n : BinaryRing K) = homogeneousComponent n R :=
    MvPolynomial.decomposition.decompose'_apply R n
  rw [hc, hc] at h
  exact h

theorem residue_zero_of_totalDegree_lt (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (P : BinaryRing K) (hP : P.totalDegree < e + t - 2) :
    residueFunctional F G e t he ht hF hG hF0 hcop (Ideal.Quotient.mk (equationsIdeal F G) P) = 0 := by
  apply (topCoordinate F G e t he ht hF hG hF0 hcop).map_eq_zero_iff.mpr
  apply Subtype.ext
  change Ideal.Quotient.mk (equationsIdeal F G) (homogeneousComponent (e + t - 2) P) = 0
  rw [homogeneousComponent_eq_zero _ _ hP, map_zero]

theorem orthogonal_component_mem (F G : BinaryRing K) (e t j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (P : BinaryRing K)
    (horth : ∀ Q : BinaryRing K, Q.totalDegree ≤ j →
      residueFunctional F G e t he ht hF hG hF0 hcop
        (Ideal.Quotient.mk (equationsIdeal F G) (P * Q)) = 0)
    (d : ℕ) (hd : e + t - 2 - j - 1 < d) :
    homogeneousComponent d P ∈ equationsIdeal F G := by
  by_cases hhigh : e + t - 1 ≤ d
  · exact homogeneous_high_mem_ideal F G e t d he ht hF hG hF0 hG0 hcop
      _ (homogeneousComponent_isHomogeneous d P) hhigh
  · by_contra hdn
    have hds : d ≤ e + t - 2 := by omega
    obtain ⟨Q, hQ, hPQ⟩ := exists_top_product F G e t d hF hG hF0 hcop
      (homogeneousComponent d P) (homogeneousComponent_isHomogeneous d P) hdn hds
    have hQd : Q.totalDegree ≤ j := hQ.totalDegree_le.trans (by omega)
    have hz := horth Q hQd
    have htop := (topCoordinate F G e t he ht hF hG hF0 hcop).injective
      (hz.trans (map_zero _).symm)
    have hval := congrArg Subtype.val htop
    change Ideal.Quotient.mk (equationsIdeal F G)
      (homogeneousComponent (e + t - 2) (P * Q)) = 0 at hval
    have hsum : d + (e + t - 2 - d) = e + t - 2 := by omega
    rw [← hsum, component_mul_homogeneous P Q d _ hQ] at hval
    exact hPQ (Ideal.Quotient.eq_zero_iff_mem.mp hval)

/-- Orthogonality to degree-at-most-j polynomials is exactly the existence
of a representative of complementary total degree. -/
theorem orthogonal_iff_low_representative (F G : BinaryRing K) (e t j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (P : BinaryRing K) (hj : j < e + t - 2) :
    (∀ Q : BinaryRing K, Q.totalDegree ≤ j →
      residueFunctional F G e t he ht hF hG hF0 hcop
        (Ideal.Quotient.mk (equationsIdeal F G) (P * Q)) = 0) ↔
      ∃ R : BinaryRing K, R.totalDegree ≤ e + t - 2 - j - 1 ∧
        Ideal.Quotient.mk (equationsIdeal F G) R = Ideal.Quotient.mk (equationsIdeal F G) P := by
  constructor
  · intro horth
    let r := e + t - 2 - j - 1
    let T := Finset.range (P.totalDegree + 1)
    let R : BinaryRing K := ∑ d ∈ T.filter (fun d => d ≤ r), homogeneousComponent d P
    let H : BinaryRing K := ∑ d ∈ T.filter (fun d => ¬d ≤ r), homogeneousComponent d P
    have hR : R.totalDegree ≤ r := by
      apply totalDegree_finsetSum_le
      intro d hd
      exact (homogeneousComponent_isHomogeneous d P).totalDegree_le.trans
        (Finset.mem_filter.mp hd).2
    have hHI : H ∈ equationsIdeal F G := by
      apply Ideal.sum_mem
      intro d hd
      exact orthogonal_component_mem F G e t j he ht hF hG hF0 hG0 hcop P horth d
        (by have hh := (Finset.mem_filter.mp hd).2; omega)
    have hsum : R + H = P :=
      (Finset.sum_filter_add_sum_filter_not T (fun d => d ≤ r)
        (fun d => homogeneousComponent d P)).trans (sum_homogeneousComponent P)
    refine ⟨R, hR, ?_⟩
    rw [← hsum, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hHI, add_zero]
  · rintro ⟨R, hR, hRP⟩ Q hQ
    rw [map_mul, ← hRP, ← map_mul]
    apply residue_zero_of_totalDegree_lt F G e t he ht hF hG hF0 hcop
    have hdeg := totalDegree_mul R Q
    omega

def filteredPiece (F G : BinaryRing K) (j : ℕ) : Submodule K (QuotientRing F G) :=
  (restrictTotalDegree (Fin 2) K j).map (Ideal.Quotient.mkₐ K (equationsIdeal F G)).toLinearMap

theorem mem_filteredPiece (F G : BinaryRing K) (j : ℕ) (a : QuotientRing F G) :
    a ∈ filteredPiece F G j ↔ ∃ P : BinaryRing K,
      P.totalDegree ≤ j ∧ Ideal.Quotient.mk (equationsIdeal F G) P = a := by
  simp only [filteredPiece, Submodule.mem_map, mem_restrictTotalDegree]
  rfl

/-- The complementary-filtration identity is proved for the actual quotient
and its actual total-degree images. -/
theorem filtered_orthogonal (F G : BinaryRing K) (e t j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) (hj : j < e + t - 2) :
    (filteredPiece F G j).dualAnnihilator.comap
      (residuePairing F G e t he ht hF hG hF0 hcop) =
        filteredPiece F G (e + t - 2 - j - 1) := by
  ext a
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator, mem_filteredPiece]
  rw [← orthogonal_iff_low_representative F G e t j he ht hF hG hF0 hG0 hcop P hj]
  constructor
  · intro h Q hQ
    have hmem := (mem_filteredPiece F G j _).mpr ⟨Q, hQ, rfl⟩
    have hh := h _ hmem
    change residueFunctional F G e t he ht hF hG hF0 hcop
      (Ideal.Quotient.mk (equationsIdeal F G) P * Ideal.Quotient.mk (equationsIdeal F G) Q) = 0 at hh
    simpa only [← map_mul] using hh
  · intro h a ha
    obtain ⟨Q, hQ, rfl⟩ := (mem_filteredPiece F G j a).mp ha
    change residueFunctional F G e t he ht hF hG hF0 hcop
      (Ideal.Quotient.mk (equationsIdeal F G) P * Ideal.Quotient.mk (equationsIdeal F G) Q) = 0
    simpa only [← map_mul] using h Q hQ

#print axioms orthogonal_iff_low_representative
#print axioms filtered_orthogonal

end Cylinder.CompleteIntersectionFiltered

end
