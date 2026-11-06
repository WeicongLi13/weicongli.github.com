module

public import Cylinder.AffineGradedCriterion

/-! Actual associated degree quotients for the affine total-degree
filtration. Their maps from homogeneous forms are surjective, and their
kernels are proved to be the degree parts of the top-equation ideal. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineAssociatedPieces

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionFiltered
open Cylinder.AffineGradedCriterion Cylinder.LeadingComponents
open scoped Classical

variable {K : Type*} [Field K]

def lowerPiece (f g : BinaryRing K) (N : ℕ) : Submodule K (filteredPiece f g N) :=
  (filteredPiece f g (N - 1)).comap (filteredPiece f g N).subtype

abbrev AssociatedPiece (f g : BinaryRing K) (N : ℕ) :=
  filteredPiece f g N ⧸ lowerPiece f g N

def homogeneousToFiltered (f g : BinaryRing K) (N : ℕ) :
    BinaryForms K N →ₗ[K] filteredPiece f g N :=
  (quotientPieceMap f g N).codRestrict _ (fun P =>
    (mem_filteredPiece f g N _).mpr ⟨P.val, P.property.totalDegree_le, rfl⟩)

def gradeMap (f g : BinaryRing K) (N : ℕ) :
    BinaryForms K N →ₗ[K] AssociatedPiece f g N :=
  (lowerPiece f g N).mkQ.comp (homogeneousToFiltered f g N)

theorem remove_component_lower (P : BinaryRing K) (N : ℕ) (hP : P.totalDegree ≤ N) :
    P - homogeneousComponent N P = 0 ∨ (P - homogeneousComponent N P).totalDegree < N := by
  apply eq_zero_or_totalDegree_lt_of_component_zero
  · exact (totalDegree_sub _ _).trans
      (max_le hP (homogeneousComponent_isHomogeneous _ _).totalDegree_le)
  · rw [map_sub, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _), sub_self]

theorem gradeMap_surjective (f g : BinaryRing K) (N : ℕ) (hN : 0 < N) :
    Function.Surjective (gradeMap f g N) := by
  intro z
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (lowerPiece f g N) z
  obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g N a.val).mp a.property
  let H : BinaryForms K N := ⟨homogeneousComponent N P, homogeneousComponent_isHomogeneous N P⟩
  refine ⟨H, ?_⟩
  apply Eq.symm
  apply (Submodule.Quotient.eq _).mpr
  change a.val - (homogeneousToFiltered f g N H).val ∈ filteredPiece f g (N - 1)
  apply (mem_filteredPiece f g (N - 1) _).mpr
  refine ⟨P - homogeneousComponent N P, ?_, ?_⟩
  · rcases remove_component_lower P N hP with h | h
    · rw [h]; simp
    · omega
  · rw [map_sub, hPa]
    rfl

theorem gradeMap_kernel (f g : BinaryRing K) (e t N : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hN : 0 < N) :
    LinearMap.ker (gradeMap f g N) =
      idealPiece (homogeneousComponent e f) (homogeneousComponent t g) N := by
  ext P
  change (Submodule.Quotient.mk (homogeneousToFiltered f g N P) : AssociatedPiece f g N) = 0 ↔
    P.val ∈ equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g)
  rw [Submodule.Quotient.mk_eq_zero]
  change Ideal.Quotient.mk (equationsIdeal f g) P.val ∈ filteredPiece f g (N - 1) ↔ _
  rw [mem_filteredPiece]
  have hc := component_mem_iff_lower_representative f g P.val e t N hf hg hfe hcop
    P.property.totalDegree_le hN
  rw [homogeneousComponent_eq_self P.property] at hc
  rw [hc]
  constructor
  · rintro ⟨Q, hQ, hQP⟩
    exact ⟨Q, by omega, hQP⟩
  · rintro ⟨Q, hQ, hQP⟩
    exact ⟨Q, by omega, hQP⟩

/-- Each positive associated degree piece is the actual corresponding
homogeneous quotient for the leading equations. -/
def associatedPieceEquiv (f g : BinaryRing K) (e t N : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hN : 0 < N) :
    (BinaryForms K N ⧸ idealPiece (homogeneousComponent e f) (homogeneousComponent t g) N) ≃ₗ[K]
      AssociatedPiece f g N := by
  have iso := (gradeMap f g N).quotKerEquivOfSurjective (gradeMap_surjective f g N hN)
  rw [gradeMap_kernel f g e t N hf hg hfe hcop hN] at iso
  exact iso

#print axioms gradeMap_surjective
#print axioms gradeMap_kernel
#print axioms associatedPieceEquiv

end Cylinder.AffineAssociatedPieces

end
