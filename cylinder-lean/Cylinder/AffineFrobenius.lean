module

public import Cylinder.AffineResidueFunctional
public import Cylinder.AffineMinimalDegree

/-! The actual nonhomogeneous complete-intersection quotient is Frobenius.
Minimal-degree representatives and complementary homogeneous products
prove nondegeneracy of its constructed residue multiplication pairing. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineFrobenius

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.CompleteIntersectionAdjoint
open Cylinder.AffineIdealLeading Cylinder.AffineGradedCriterion Cylinder.AffineMinimalDegree
open Cylinder.FrobeniusAnnihilator
open Cylinder.AffineResidueFunctional
open scoped Classical

variable {K : Type*} [Field K]
variable (f g : BinaryRing K) (e t : ℕ)
variable (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
variable (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
variable (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
include he ht hf hg hfe hge hcop

/-- The complementary product is an actual polynomial of the indicated
homogeneous degree; its residue is nonzero in the actual affine quotient. -/
theorem exists_residue_product_of_minimal (P : BinaryRing K)
    (hP : Ideal.Quotient.mk (equationsIdeal f g) P ≠ 0) (hPdeg : P.totalDegree ≤ e + t - 2)
    (hmin : ∀ Q : BinaryRing K,
      Ideal.Quotient.mk (equationsIdeal f g) Q = Ideal.Quotient.mk (equationsIdeal f g) P →
        P.totalDegree ≤ Q.totalDegree) :
    ∃ Q : BinaryRing K, Q.IsHomogeneous (e + t - 2 - P.totalDegree) ∧
      residueFunctional f g e t he ht hf hg hfe hge hcop
        (Ideal.Quotient.mk (equationsIdeal f g) (P * Q)) ≠ 0 := by
  have htop := minimal_top_not_mem f g P e t hf hg hP hmin
  obtain ⟨Q, hQ, hPQ⟩ := exists_top_product (homogeneousComponent e f) (homogeneousComponent t g)
    e t P.totalDegree (homogeneousComponent_isHomogeneous e f)
    (homogeneousComponent_isHomogeneous t g) hfe hcop
    (homogeneousComponent P.totalDegree P) (homogeneousComponent_isHomogeneous _ _) htop hPdeg
  refine ⟨Q, hQ, ?_⟩
  intro hz
  have hmem := (residueFunctional_eq_zero_iff f g e t he ht hf hg hfe hge hcop _).mp hz
  have hcomp : homogeneousComponent (e + t - 2) (P * Q) =
      homogeneousComponent P.totalDegree P * Q := by
    have hsum : P.totalDegree + (e + t - 2 - P.totalDegree) = e + t - 2 := by omega
    rw [← hsum, component_mul_homogeneous P Q _ _ hQ]
  have hproddeg : (P * Q).totalDegree ≤ e + t - 2 := by
    have h := totalDegree_mul P Q
    have hqd := hQ.totalDegree_le
    omega
  by_cases hσ : e + t - 2 = 0
  · rw [topBoundary, if_pos hσ] at hmem
    have hzero : Ideal.Quotient.mk (equationsIdeal f g) (P * Q) = 0 := hmem
    have hPI := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hlead := top_component_mem_leading_ideal f g (P * Q) e t hf hg hfe hcop hPI
    have hdegzero : (P * Q).totalDegree = 0 := by omega
    have hlead' : homogeneousComponent (e + t - 2) (P * Q) ∈
        equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) := by
      simpa only [hσ, hdegzero] using hlead
    rw [hcomp] at hlead'
    exact hPQ hlead'
  · rw [topBoundary, if_neg hσ] at hmem
    obtain ⟨R, hRdeg, hRPQ⟩ := (mem_filteredPiece f g (e + t - 2 - 1) _).mp hmem
    have hlead := (component_mem_iff_lower_representative f g (P * Q) e t (e + t - 2)
      hf hg hfe hcop hproddeg (by omega)).mpr ⟨R, by omega, hRPQ⟩
    rw [hcomp] at hlead
    exact hPQ hlead

theorem exists_nonzero_residue_product (a : QuotientRing f g) (ha : a ≠ 0) :
    ∃ b : QuotientRing f g, residueFunctional f g e t he ht hf hg hfe hge hcop (a * b) ≠ 0 := by
  obtain ⟨P, hPa, hPdeg, hmin⟩ := exists_minimal_low_representative
    f g e t he ht hf hg hfe hge hcop a
  obtain ⟨Q, hQ, hPQ⟩ := exists_residue_product_of_minimal f g e t he ht hf hg hfe hge hcop
    P (by simpa only [hPa] using ha) hPdeg (by simpa only [hPa] using hmin)
  refine ⟨Ideal.Quotient.mk (equationsIdeal f g) Q, ?_⟩
  rw [← hPa, ← map_mul]
  exact hPQ

theorem residuePairing_injective :
    Function.Injective (multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra han
  obtain ⟨b, hb⟩ := exists_nonzero_residue_product f g e t he ht hf hg hfe hge hcop a han
  exact hb (congrArg (fun F : QuotientRing f g →ₗ[K] K => F b) ha)

/-- Perfectness is proved on the genuine finite affine algebra. -/
theorem residuePairing_isPerfPair :
    (multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop)).IsPerfPair := by
  letI := AffineFilteredAlgebra.quotient_finiteDimensional f g e t he ht hf hg hfe hge hcop
  have hi := residuePairing_injective f g e t he ht hf hg hfe hge hcop
  apply LinearMap.IsPerfPair.of_injective hi
  have hflip : (multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop)).flip =
      multiplicationPairing (residueFunctional f g e t he ht hf hg hfe hge hcop) := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change residueFunctional f g e t he ht hf hg hfe hge hcop (b * a) =
      residueFunctional f g e t he ht hf hg hfe hge hcop (a * b)
    rw [mul_comm]
  rw [hflip]
  exact hi

/-- The actual affine ideal annihilator identifies with the quotient dual,
with no pairing or residual-length hypothesis. -/
def annihilatorEquiv (J : Ideal (QuotientRing f g)) :
    J.annihilator.restrictScalars K ≃ₗ[K] Dual K (QuotientRing f g ⧸ J) :=
  annihilatorEquivDualQuotient (residueFunctional f g e t he ht hf hg hfe hge hcop)
    (residuePairing_isPerfPair f g e t he ht hf hg hfe hge hcop) J

#print axioms exists_residue_product_of_minimal
#print axioms residuePairing_isPerfPair
#print axioms annihilatorEquiv

end Cylinder.AffineFrobenius

end
