module

public import Cylinder.AffineFrobenius

/-! Complementary filtration duality on the actual nonhomogeneous affine
complete-intersection algebra. This part needs no residual-length or
pairing hypothesis. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineFilteredDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffineMinimalDegree
open Cylinder.AffineResidueFunctional Cylinder.AffineFrobenius
open Cylinder.FrobeniusAnnihilator
open scoped Classical

variable {K : Type*} [Field K]
variable (f g : BinaryRing K) (e t : ℕ)
variable (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
variable (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
variable (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
include he ht hf hg hfe hge hcop

theorem residue_zero_of_low_degree (P : BinaryRing K) (hP : P.totalDegree < e + t - 2) :
    residueFunctional f g e t he ht hf hg hfe hge hcop
      (Ideal.Quotient.mk (equationsIdeal f g) P) = 0 := by
  apply (residueFunctional_eq_zero_iff f g e t he ht hf hg hfe hge hcop _).mpr
  have hσ : e + t - 2 ≠ 0 := by omega
  rw [topBoundary, if_neg hσ]
  exact (mem_filteredPiece f g _ _).mpr ⟨P, by omega, rfl⟩

/-- Orthogonality to the actual degree-j filtration equals the actual
complementary degree filtration, also for nonhomogeneous equations. -/
theorem filtered_orthogonal (j : ℕ) (hj : j < e + t - 2) :
    (filteredPiece f g j).dualAnnihilator.comap
      (multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop)) =
        filteredPiece f g (e + t - 2 - j - 1) := by
  ext a
  constructor
  · intro ha
    have horth := (Submodule.mem_dualAnnihilator _).mp ha
    by_cases ha0 : a = 0
    · rw [ha0]; exact Submodule.zero_mem _
    · obtain ⟨P, hPa, hPdeg, hmin⟩ := exists_minimal_low_representative
        f g e t he ht hf hg hfe hge hcop a
      have hlow : P.totalDegree ≤ e + t - 2 - j - 1 := by
        by_contra hn
        obtain ⟨Q, hQ, hPQ⟩ := exists_residue_product_of_minimal f g e t he ht hf hg hfe hge hcop
          P (by simpa only [hPa] using ha0) hPdeg (by simpa only [hPa] using hmin)
        have hQdeg : Q.totalDegree ≤ j := hQ.totalDegree_le.trans (by omega)
        have hmem := (mem_filteredPiece f g j _).mpr ⟨Q, hQdeg, rfl⟩
        have hzero := horth _ hmem
        change residueFunctional f g e t he ht hf hg hfe hge hcop
          (a * Ideal.Quotient.mk (equationsIdeal f g) Q) = 0 at hzero
        rw [← hPa, ← map_mul] at hzero
        exact hPQ hzero
      exact (mem_filteredPiece f g _ _).mpr ⟨P, hlow, hPa⟩
  · intro ha
    obtain ⟨P, hPdeg, hPa⟩ := (mem_filteredPiece f g _ a).mp ha
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro b hb
    obtain ⟨Q, hQdeg, hQb⟩ := (mem_filteredPiece f g j b).mp hb
    change residueFunctional f g e t he ht hf hg hfe hge hcop (a * b) = 0
    rw [← hPa, ← hQb, ← map_mul]
    apply residue_zero_of_low_degree f g e t he ht hf hg hfe hge hcop
    have hprod := totalDegree_mul P Q
    omega

def relationSpace (f g : BinaryRing K) (J : Ideal (QuotientRing f g)) (j : ℕ) :
    Submodule K (Dual K (QuotientRing f g)) :=
  (J.restrictScalars K).dualAnnihilator ⊓ (filteredPiece f g j).dualAnnihilator

/-- Functionals factoring through `A/J` and vanishing on `F_j A` are
exactly the filtered actual annihilator, as actual vector spaces. -/
def filteredAnnihilatorEquivRelations (J : Ideal (QuotientRing f g)) (j : ℕ) (hj : j < e + t - 2) :
    ↥(J.annihilator.restrictScalars K ⊓ filteredPiece f g (e + t - 2 - j - 1)) ≃ₗ[K]
      relationSpace f g J j := by
  let ρ := residueFunctional f g e t he ht hf hg hfe hge hcop
  let p := multiplicationPairing ρ
  have hp : p.IsPerfPair := residuePairing_isPerfPair f g e t he ht hf hg hfe hge hcop
  have heq : J.annihilator.restrictScalars K ⊓ filteredPiece f g (e + t - 2 - j - 1) =
      (relationSpace f g J j).comap p := by
    rw [relationSpace, Submodule.comap_inf]
    rw [← annihilator_eq_orthogonal ρ hp J,
      filtered_orthogonal f g e t he ht hf hg hfe hge hcop j hj]
  let iso : (relationSpace f g J j).comap p ≃ₗ[K] relationSpace f g J j :=
    LinearEquiv.ofBijective (p.submoduleComap (relationSpace f g J j)) ⟨by
      intro a b hab
      apply Subtype.ext
      exact hp.bijective_left.injective (congrArg Subtype.val hab),
      LinearMap.submoduleComap_surjective_of_surjective _ _ hp.bijective_left.surjective⟩
  exact (LinearEquiv.ofEq _ _ heq).trans iso

#print axioms filtered_orthogonal
#print axioms filteredAnnihilatorEquivRelations

end Cylinder.AffineFilteredDuality

end
