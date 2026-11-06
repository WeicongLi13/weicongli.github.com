module

public import Cylinder.AffineAssociatedPieces

/-! A genuine residue functional on the nonhomogeneous affine quotient.
The quotient by the penultimate total-degree filtration is proved one
dimensional, including the linear-linear case with socle degree zero. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineResidueFunctional

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionSocle Cylinder.BinaryCompleteIntersectionGraded
open Cylinder.CompleteIntersectionFiltered Cylinder.AffineAssociatedPieces
open Cylinder.AffineIdealLeading Cylinder.AffineIdealReduction
open scoped Classical

variable {K : Type*} [Field K]
variable (f g : BinaryRing K) (e t : ℕ)
variable (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
variable (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
variable (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))

include he ht hf hg hfe hge hcop

theorem filtered_top : filteredPiece f g (e + t - 2) = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, hQ, hQP⟩ := AffineFilteredAlgebra.exists_low_degree_representative
    f g e t he ht hf hg hfe hge hcop P
  exact (mem_filteredPiece f g _ _).mpr ⟨Q, hQ, hQP⟩

def topBoundary (f g : BinaryRing K) (σ : ℕ) : Submodule K (QuotientRing f g) :=
  if σ = 0 then ⊥ else filteredPiece f g (σ - 1)

theorem constant_in_ideal_zero (P : BinaryRing K) (hP : P.totalDegree = 0)
    (hPI : P ∈ equationsIdeal f g) : P = 0 := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_bounded_representation f g P e t hf hg hfe hcop hPI
  have hA0 : A = 0 := hA.elim id (fun h => by rw [hP] at h; omega)
  have hB0 : B = 0 := hB.elim id (fun h => by rw [hP] at h; omega)
  simpa [hA0, hB0] using hAB.symm

theorem quotient_finrank_of_socle_zero (hσ : e + t - 2 = 0) :
    finrank K (QuotientRing f g) = 1 := by
  letI := AffineFilteredAlgebra.quotient_finiteDimensional f g e t he ht hf hg hfe hge hcop
  have hinj : Function.Injective (quotientPieceMap f g 0) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hP
    apply Subtype.ext
    exact constant_in_ideal_zero f g e t he ht hf hg hfe hge hcop P.val
      (Nat.eq_zero_of_le_zero P.property.totalDegree_le) (Ideal.Quotient.eq_zero_iff_mem.mp hP)
  have hsurj : Function.Surjective (quotientPieceMap f g 0) := by
    intro a
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨Q, hQ, hQP⟩ := AffineFilteredAlgebra.exists_low_degree_representative
      f g e t he ht hf hg hfe hge hcop P
    rw [hσ] at hQ
    exact ⟨⟨Q, (totalDegree_zero_iff_isHomogeneous (Fin 2)).mp (Nat.eq_zero_of_le_zero hQ)⟩, hQP⟩
  have hdim := (LinearEquiv.ofBijective (quotientPieceMap f g 0) ⟨hinj, hsurj⟩).finrank_eq
  rw [binaryForms_finrank] at hdim
  exact hdim.symm

theorem associated_top_finrank (hσ : 0 < e + t - 2) :
    finrank K (AssociatedPiece f g (e + t - 2)) = 1 := by
  letI := AffineFilteredAlgebra.quotient_finiteDimensional f g e t he ht hf hg hfe hge hcop
  rw [← (associatedPieceEquiv f g e t (e + t - 2) hf hg hfe hcop hσ).finrank_eq]
  rw [← quotientPieceMap_kernel]
  rw [(quotientPieceMap (homogeneousComponent e f) (homogeneousComponent t g)
    (e + t - 2)).quotKerEquivRange.finrank_eq]
  exact top_quotientPiece_finrank _ _ e t he ht
    (homogeneousComponent_isHomogeneous e f) (homogeneousComponent_isHomogeneous t g) hfe hcop

theorem topQuotient_finrank :
    finrank K (QuotientRing f g ⧸ topBoundary f g (e + t - 2)) = 1 := by
  letI := AffineFilteredAlgebra.quotient_finiteDimensional f g e t he ht hf hg hfe hge hcop
  by_cases hσ : e + t - 2 = 0
  · rw [topBoundary, if_pos hσ]
    rw [((⊥ : Submodule K (QuotientRing f g)).quotEquivOfEqBot rfl).finrank_eq]
    exact quotient_finrank_of_socle_zero f g e t he ht hf hg hfe hge hcop hσ
  · rw [topBoundary, if_neg hσ]
    have htop := filtered_top f g e t he ht hf hg hfe hge hcop
    have hlow : finrank K (lowerPiece f g (e + t - 2)) =
        finrank K (filteredPiece f g (e + t - 2 - 1)) := by
      rw [← Submodule.finrank_map_subtype_eq (filteredPiece f g (e + t - 2))
        (lowerPiece f g (e + t - 2))]
      unfold lowerPiece
      rw [Submodule.map_comap_subtype, htop, top_inf_eq]
    have ha := (lowerPiece f g (e + t - 2)).finrank_quotient_add_finrank
    have hq := (filteredPiece f g (e + t - 2 - 1)).finrank_quotient_add_finrank
    have hatop := associated_top_finrank f g e t he ht hf hg hfe hge hcop (by omega)
    change finrank K (AssociatedPiece f g (e + t - 2)) +
      finrank K (lowerPiece f g (e + t - 2)) = finrank K (filteredPiece f g (e + t - 2)) at ha
    rw [hatop, hlow, htop, finrank_top] at ha
    omega

def residueCoordinate :
    (QuotientRing f g ⧸ topBoundary f g (e + t - 2)) ≃ₗ[K] K := by
  letI := AffineFilteredAlgebra.quotient_finiteDimensional f g e t he ht hf hg hfe hge hcop
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [topQuotient_finrank f g e t he ht hf hg hfe hge hcop, Module.finrank_self])

def residueFunctional : QuotientRing f g →ₗ[K] K :=
  (residueCoordinate f g e t he ht hf hg hfe hge hcop).toLinearMap.comp
    (topBoundary f g (e + t - 2)).mkQ

theorem residueFunctional_eq_zero_iff (a : QuotientRing f g) :
    residueFunctional f g e t he ht hf hg hfe hge hcop a = 0 ↔
      a ∈ topBoundary f g (e + t - 2) := by
  change residueCoordinate f g e t he ht hf hg hfe hge hcop
    (Submodule.Quotient.mk a) = 0 ↔ _
  rw [(residueCoordinate f g e t he ht hf hg hfe hge hcop).map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]

#print axioms topQuotient_finrank
#print axioms residueFunctional
#print axioms residueFunctional_eq_zero_iff

end Cylinder.AffineResidueFunctional

end
