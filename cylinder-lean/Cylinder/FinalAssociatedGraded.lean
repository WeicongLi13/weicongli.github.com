module

public import Cylinder.FinalHomogeneousQuotient
public import Mathlib.Algebra.Ring.TransferInstance

/-! Proposition 5.2: the actual direct sum of the total-degree filtration
quotients is the quotient by the two leading equations.  The zero piece
uses zero as its predecessor.  Multiplication is verified on arbitrary
filtered representatives, and the isomorphism preserves every degree. -/

@[expose] public section
noncomputable section

namespace Cylinder.FinalAssociatedGraded

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionFiltered
open Cylinder.FinalAssociatedPieces
open scoped Classical DirectSum

variable {K : Type*} [Field K]

structure LeadingData (f g : BinaryRing K) (e t : ℕ) : Prop where
  degree_f : f.totalDegree = e
  degree_g : g.totalDegree = t
  top_f_ne_zero : homogeneousComponent e f ≠ 0
  coprime : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g)

abbrev Associated (f g : BinaryRing K) := ⨁ n : ℕ, Piece f g n

instance associatedAddCommGroup (f g : BinaryRing K) : AddCommGroup (Associated f g) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, Piece f g n))

abbrev LeadingQuotient (f g : BinaryRing K) (e t : ℕ) :=
  QuotientRing (homogeneousComponent e f) (homogeneousComponent t g)

variable {f g : BinaryRing K} {e t : ℕ} (d : LeadingData f g e t)

def sumEquiv : Associated f g ≃ₗ[K] LeadingQuotient f g e t :=
  (DFinsupp.mapRange.linearEquiv (fun n =>
    (pieceEquiv f g e t n d.degree_f d.degree_g d.top_f_ne_zero d.coprime).symm)).trans
    (FinalHomogeneousQuotient.quotientEquiv (homogeneousComponent e f)
      (homogeneousComponent t g) e t (homogeneousComponent_isHomogeneous e f)
      (homogeneousComponent_isHomogeneous t g)).symm

theorem sumEquiv_homogeneous (n : ℕ) (P : BinaryForms K n) :
    sumEquiv d (DirectSum.lof K ℕ (Piece f g) n (gradeMap f g n P)) =
      Ideal.Quotient.mk (equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g)) P.val := by
  have hpiece :
      (pieceEquiv f g e t n d.degree_f d.degree_g d.top_f_ne_zero d.coprime).symm
        (gradeMap f g n P) = Submodule.Quotient.mk P := by
    rw [← pieceEquiv_mk f g e t n d.degree_f d.degree_g d.top_f_ne_zero d.coprime P,
      LinearEquiv.symm_apply_apply]
  change (FinalHomogeneousQuotient.quotientEquiv _ _ e t _ _).symm
    (DFinsupp.mapRange (fun n =>
      (pieceEquiv f g e t n d.degree_f d.degree_g d.top_f_ne_zero d.coprime).symm)
      (fun n => (pieceEquiv f g e t n d.degree_f d.degree_g d.top_f_ne_zero d.coprime).symm.map_zero)
      (DFinsupp.single n (gradeMap f g n P))) = _
  rw [DFinsupp.mapRange_single, hpiece]
  exact FinalHomogeneousQuotient.quotientEquiv_symm_lof _ _ e t n _ _ P

def filteredClass (f g : BinaryRing K) (n : ℕ) (P : BinaryRing K) (hP : P.totalDegree ≤ n) :
    Piece f g n :=
  Submodule.Quotient.mk ⟨Ideal.Quotient.mk (equationsIdeal f g) P,
    (mem_filteredPiece f g n _).mpr ⟨P, hP, rfl⟩⟩

theorem filteredClass_eq_top (f g : BinaryRing K) (n : ℕ) (P : BinaryRing K)
    (hP : P.totalDegree ≤ n) :
    filteredClass f g n P hP =
      gradeMap f g n ⟨homogeneousComponent n P, homogeneousComponent_isHomogeneous n P⟩ := by
  apply (Submodule.Quotient.eq _).mpr
  change (⟨Ideal.Quotient.mk (equationsIdeal f g) P, _⟩ -
      Cylinder.AffineAssociatedPieces.homogeneousToFiltered f g n
        ⟨homogeneousComponent n P, homogeneousComponent_isHomogeneous n P⟩) ∈ lowerPiece f g n
  by_cases hn : n = 0
  · subst n
    rw [lowerPiece, if_pos rfl]
    rw [Submodule.mem_bot]
    apply Subtype.ext
    change Ideal.Quotient.mk (equationsIdeal f g) P -
      Ideal.Quotient.mk (equationsIdeal f g) (homogeneousComponent 0 P) = 0
    rw [← map_sub]
    rcases Cylinder.AffineAssociatedPieces.remove_component_lower P 0 hP with h | h
    · rw [h, map_zero]
    · omega
  · rw [lowerPiece, if_neg hn]
    change Ideal.Quotient.mk (equationsIdeal f g) P -
      Ideal.Quotient.mk (equationsIdeal f g) (homogeneousComponent n P) ∈ filteredPiece f g (n - 1)
    apply (mem_filteredPiece f g (n - 1) _).mpr
    refine ⟨P - homogeneousComponent n P, ?_, map_sub _ _ _⟩
    rcases Cylinder.AffineAssociatedPieces.remove_component_lower P n hP with h | h
    · rw [h]; simp
    · omega

theorem sumEquiv_filteredClass (n : ℕ) (P : BinaryRing K) (hP : P.totalDegree ≤ n) :
    sumEquiv d (DirectSum.lof K ℕ (Piece f g) n (filteredClass f g n P hP)) =
      Ideal.Quotient.mk (equationsIdeal (homogeneousComponent e f) (homogeneousComponent t g))
        (homogeneousComponent n P) := by
  rw [filteredClass_eq_top]
  exact sumEquiv_homogeneous d n _

/-- This ring structure keeps the existing direct-sum addition. Its product
is characterized below by multiplication of actual filtered representatives. -/
@[instance_reducible] def ringStructure : CommRing (Associated f g) := by
  let E := sumEquiv d
  letI : One (Associated f g) := ⟨E.symm 1⟩
  letI : Mul (Associated f g) := ⟨fun a b => E.symm (E a * E b)⟩
  letI : Pow (Associated f g) ℕ := ⟨fun a n => E.symm (E a ^ n)⟩
  letI : NatCast (Associated f g) := ⟨fun n => E.symm n⟩
  letI : IntCast (Associated f g) := ⟨fun n => E.symm n⟩
  exact E.injective.commRing E E.map_zero (E.apply_symm_apply 1)
    E.map_add (fun a b => E.apply_symm_apply (E a * E b)) E.map_neg E.map_sub
    (fun n a => map_nsmul E n a) (fun n a => map_zsmul E n a)
    (fun a n => E.apply_symm_apply (E a ^ n))
    (fun n => E.apply_symm_apply n) (fun n => E.apply_symm_apply n)

def associatedRingEquiv :
    letI := ringStructure d
    Associated f g ≃+* LeadingQuotient f g e t := by
  letI := ringStructure d
  exact { (sumEquiv d).toAddEquiv with
    map_mul' := fun a b => (sumEquiv d).apply_symm_apply _ }

theorem associatedRingEquiv_apply (a : Associated f g) :
    associatedRingEquiv d a = sumEquiv d a := rfl

/-- The product is exactly the multiplication prescribed in Proposition 5.2,
for arbitrary bounded polynomial representatives, including degree zero. -/
theorem multiplication_representatives (i j : ℕ) (P Q : BinaryRing K)
    (hP : P.totalDegree ≤ i) (hQ : Q.totalDegree ≤ j) :
    letI := ringStructure d
    DirectSum.lof K ℕ (Piece f g) i (filteredClass f g i P hP) *
      DirectSum.lof K ℕ (Piece f g) j (filteredClass f g j Q hQ) =
        DirectSum.lof K ℕ (Piece f g) (i + j)
          (filteredClass f g (i + j) (P * Q)
            ((totalDegree_mul P Q).trans (Nat.add_le_add hP hQ))) := by
  letI := ringStructure d
  apply (associatedRingEquiv d).injective
  rw [map_mul]
  simp only [associatedRingEquiv_apply, sumEquiv_filteredClass]
  rw [Cylinder.LeadingComponents.highest_component_mul P Q i j hP hQ, map_mul]

def filteredProduct {i j : ℕ} (a : filteredPiece f g i) (b : filteredPiece f g j) :
    filteredPiece f g (i + j) :=
  ⟨a.val * b.val, by
    obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g i a.val).mp a.property
    obtain ⟨Q, hQ, hQb⟩ := (mem_filteredPiece f g j b.val).mp b.property
    exact (mem_filteredPiece f g (i + j) _).mpr
      ⟨P * Q, (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ), by rw [map_mul, hPa, hQb]⟩⟩

/-- Multiplication of two classes in the actual filtration quotients. -/
theorem multiplication_filtered_classes (i j : ℕ)
    (a : filteredPiece f g i) (b : filteredPiece f g j) :
    letI := ringStructure d
    DirectSum.lof K ℕ (Piece f g) i (Submodule.Quotient.mk a) *
      DirectSum.lof K ℕ (Piece f g) j (Submodule.Quotient.mk b) =
        DirectSum.lof K ℕ (Piece f g) (i + j) (Submodule.Quotient.mk (filteredProduct a b)) := by
  letI := ringStructure d
  obtain ⟨P, hP, hPa⟩ := (mem_filteredPiece f g i a.val).mp a.property
  obtain ⟨Q, hQ, hQb⟩ := (mem_filteredPiece f g j b.val).mp b.property
  have ha : a = ⟨Ideal.Quotient.mk (equationsIdeal f g) P,
      (mem_filteredPiece f g i _).mpr ⟨P, hP, rfl⟩⟩ := Subtype.ext hPa.symm
  have hb : b = ⟨Ideal.Quotient.mk (equationsIdeal f g) Q,
      (mem_filteredPiece f g j _).mpr ⟨Q, hQ, rfl⟩⟩ := Subtype.ext hQb.symm
  have hab : filteredProduct a b =
      ⟨Ideal.Quotient.mk (equationsIdeal f g) (P * Q),
        (mem_filteredPiece f g (i + j) _).mpr
          ⟨P * Q, (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ), rfl⟩⟩ := by
    apply Subtype.ext
    change a.val * b.val = Ideal.Quotient.mk (equationsIdeal f g) (P * Q)
    rw [← hPa, ← hQb, map_mul]
  rw [hab, ha, hb]
  exact multiplication_representatives d i j P Q hP hQ

/-- Every degree is preserved, so this is a graded ring isomorphism. -/
theorem degree_preserving (n : ℕ) :
    Submodule.map (sumEquiv d).toLinearMap
      (LinearMap.range (DirectSum.lof K ℕ (Piece f g) n)) =
        quotientPiece (homogeneousComponent e f) (homogeneousComponent t g) n := by
  ext z
  constructor
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    obtain ⟨P, rfl⟩ := gradeMap_surjective f g n b
    exact ⟨P, (sumEquiv_homogeneous d n P).symm⟩
  · rintro ⟨P, rfl⟩
    refine ⟨DirectSum.lof K ℕ (Piece f g) n (gradeMap f g n P),
      ⟨gradeMap f g n P, rfl⟩, ?_⟩
    exact sumEquiv_homogeneous d n P

end Cylinder.FinalAssociatedGraded

end
