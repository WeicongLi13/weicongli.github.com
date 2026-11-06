module

public import Cylinder.AffineAssociatedPieces

/-! The total-degree associated pieces, including degree zero.  The
predecessor of degree zero is the zero submodule, not the degree-zero
filtered piece. -/

@[expose] public section
noncomputable section

namespace Cylinder.FinalAssociatedPieces

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionFiltered
open Cylinder.AffineGradedCriterion Cylinder.AffineIdealLeading
open scoped Classical

variable {K : Type*} [Field K]

def lowerPiece (f g : BinaryRing K) (n : ℕ) : Submodule K (filteredPiece f g n) :=
  if n = 0 then ⊥ else Cylinder.AffineAssociatedPieces.lowerPiece f g n

abbrev Piece (f g : BinaryRing K) (n : ℕ) :=
  filteredPiece f g n ⧸ lowerPiece f g n

instance pieceAddCommGroup (f g : BinaryRing K) (n : ℕ) : AddCommGroup (Piece f g n) :=
  Submodule.Quotient.addCommGroup (lowerPiece f g n)

def gradeMap (f g : BinaryRing K) (n : ℕ) : BinaryForms K n →ₗ[K] Piece f g n :=
  (lowerPiece f g n).mkQ.comp (Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g n)

theorem gradeMap_surjective (f g : BinaryRing K) (n : ℕ) :
    Function.Surjective (gradeMap f g n) := by
  by_cases hn : n = 0
  · subst n
    intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (lowerPiece f g 0) z
    obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g 0 a.val).mp a.property
    have hhom : P.IsHomogeneous 0 := by
      have h := Cylinder.AffineAssociatedPieces.remove_component_lower P 0 hP
      rcases h with h | h
      · have heq : P = homogeneousComponent 0 P := sub_eq_zero.mp h
        rw [heq]
        exact homogeneousComponent_isHomogeneous _ _
      · omega
    refine ⟨⟨P, hhom⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk a
    congr 1
    exact Subtype.ext hPa
  · intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (lowerPiece f g n) z
    obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g n a.val).mp a.property
    let H : BinaryForms K n := ⟨homogeneousComponent n P, homogeneousComponent_isHomogeneous n P⟩
    refine ⟨H, ?_⟩
    apply Eq.symm
    apply (Submodule.Quotient.eq _).mpr
    change a - Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g n H ∈ lowerPiece f g n
    rw [lowerPiece, if_neg hn]
    change a.val - (Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g n H).val ∈
      filteredPiece f g (n - 1)
    apply (mem_filteredPiece f g (n - 1) _).mpr
    refine ⟨P - homogeneousComponent n P, ?_, ?_⟩
    · rcases Cylinder.AffineAssociatedPieces.remove_component_lower P n hP with h | h
      · rw [h]; simp
      · omega
    · rw [map_sub, hPa]
      rfl

theorem gradeMap_kernel (f g : BinaryRing K) (e t n : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    LinearMap.ker (gradeMap f g n) =
      idealPiece (homogeneousComponent e f) (homogeneousComponent t g) n := by
  by_cases hn : n = 0
  · subst n
    ext P
    change Submodule.Quotient.mk _ = (0 : Piece f g 0) ↔
      P.val ∈ equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g)
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [lowerPiece, if_pos rfl, Submodule.mem_bot]
    change Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g 0 P = 0 ↔ _
    constructor
    · intro h
      have hz : Ideal.Quotient.mk (equationsIdeal f g) P.val = 0 := congrArg Subtype.val h
      have hI := Ideal.Quotient.eq_zero_iff_mem.mp hz
      have hd : P.val.totalDegree = 0 := Nat.eq_zero_of_le_zero P.property.totalDegree_le
      have ht := top_component_mem_leading_ideal f g P.val e t hf hg hfe hcop hI
      simpa only [hd, homogeneousComponent_eq_self P.property] using ht
    · intro hI
      have htop : homogeneousComponent 0 P.val ∈
          equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g) := by
        simpa only [homogeneousComponent_eq_self P.property] using hI
      obtain ⟨Q, hQ, hQP⟩ := lower_representative_of_component_mem f g P.val e t 0 hf hg
        P.property.totalDegree_le htop
      have hQ0 : Q = 0 := hQ.resolve_right (by omega)
      apply Subtype.ext
      change Ideal.Quotient.mk (equationsIdeal f g) P.val = 0
      rw [hQ0, map_zero] at hQP
      exact hQP.symm
  · ext P
    change Submodule.Quotient.mk _ = (0 : Piece f g n) ↔
      P.val ∈ equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g)
    rw [Submodule.Quotient.mk_eq_zero]
    change Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g n P ∈ lowerPiece f g n ↔ _
    rw [lowerPiece, if_neg hn]
    change Ideal.Quotient.mk (equationsIdeal f g) P.val ∈ filteredPiece f g (n - 1) ↔ _
    rw [mem_filteredPiece]
    have hc := component_mem_iff_lower_representative f g P.val e t n hf hg hfe hcop
      P.property.totalDegree_le (Nat.pos_of_ne_zero hn)
    rw [homogeneousComponent_eq_self P.property] at hc
    rw [hc]
    constructor
    · rintro ⟨Q, hQ, hQP⟩
      exact ⟨Q, by omega, hQP⟩
    · rintro ⟨Q, hQ, hQP⟩
      exact ⟨Q, by omega, hQP⟩

def pieceMap (f g : BinaryRing K) (e t n : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    (BinaryForms K n ⧸ idealPiece (homogeneousComponent e f) (homogeneousComponent t g) n)
      →ₗ[K] Piece f g n :=
  (idealPiece (homogeneousComponent e f) (homogeneousComponent t g) n).liftQ
    (gradeMap f g n) (le_of_eq (gradeMap_kernel f g e t n hf hg hfe hcop).symm)

def pieceEquiv (f g : BinaryRing K) (e t n : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)) :
    (BinaryForms K n ⧸ idealPiece (homogeneousComponent e f) (homogeneousComponent t g) n)
      ≃ₗ[K] Piece f g n :=
  LinearEquiv.ofBijective (pieceMap f g e t n hf hg hfe hcop) ⟨by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot' _ _ (gradeMap_kernel f g e t n hf hg hfe hcop).symm,
    by
      intro z
      obtain ⟨P, hP⟩ := gradeMap_surjective f g n z
      exact ⟨Submodule.Quotient.mk P, hP⟩⟩

theorem pieceEquiv_mk (f g : BinaryRing K) (e t n : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (P : BinaryForms K n) :
    pieceEquiv f g e t n hf hg hfe hcop (Submodule.Quotient.mk P) = gradeMap f g n P := rfl

end Cylinder.FinalAssociatedPieces

end
