module

public import Cylinder.CompleteIntersectionKoszul
public import Mathlib.RingTheory.Ideal.Colon

/-! Actual equations, residual colon ideals and graded residual quotient
pieces are transported by degree-preserving coordinate algebra equivalences. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualCoordinateTransport

open Module Cylinder.CompleteIntersectionKoszul
open scoped Classical

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

theorem comap_colon (e : R ≃ₐ[K] S) (J L : Ideal S) :
    Ideal.comap e (J.colon (L : Set S)) =
      (Ideal.comap e J).colon ((Ideal.comap e L : Ideal R) : Set R) := by
  ext x
  constructor
  · intro hx
    apply Submodule.mem_colon.mpr
    intro y hy
    change e (x * y) ∈ J
    rw [map_mul]
    exact Submodule.mem_colon.mp hx (e y) hy
  · intro hx
    apply Submodule.mem_colon.mpr
    intro y hy
    change y ∈ L at hy
    have hpre : e.symm y ∈ Ideal.comap e L := by
      change e (e.symm y) ∈ L
      rw [e.apply_symm_apply]
      exact hy
    have hxy := Submodule.mem_colon.mp hx (e.symm y) hpre
    change e (x * e.symm y) ∈ J at hxy
    change e x * y ∈ J
    rw [map_mul, e.apply_symm_apply] at hxy
    exact hxy

theorem equationsIdeal_comap (e : R ≃ₐ[K] S) (F G : R) :
    Ideal.comap e (equationsIdeal (e F) (e G)) = equationsIdeal F G := by
  ext H
  constructor
  · intro hH
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hH
    refine Ideal.mem_span_pair.mpr ⟨e.symm A, e.symm B, ?_⟩
    apply e.injective
    simpa only [map_add, map_mul, e.apply_symm_apply] using hAB
  · intro hH
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hH
    exact Ideal.mem_span_pair.mpr ⟨e A, e B, by simpa only [map_add, map_mul] using congrArg e hAB⟩

theorem residualIdeal_comap (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D) :
    Ideal.comap e (J.colon (E : Set S)) = I.colon (D : Set R) := by
  rw [comap_colon, hI, hD]

def residualPiece (I D : Ideal R) (A : ℤ → Submodule K R) (d : ℤ) : Submodule K R :=
  (I.colon (D : Set R)).restrictScalars K ⊓ A d

def equationPiece (I D : Ideal R) (A : ℤ → Submodule K R) (d : ℤ) :
    Submodule K (residualPiece I D A d) :=
  (I.restrictScalars K).comap (residualPiece I D A d).subtype

abbrev ResidualQuotient (I D : Ideal R) (A : ℤ → Submodule K R) (d : ℤ) : Type _ :=
  @HasQuotient.Quotient ↥(residualPiece I D A d) _
    (Submodule.hasQuotient (R := K)) (equationPiece I D A d)

def residualPieceEquiv (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (A : ℤ → Submodule K R) (B : ℤ → Submodule K S) (d : ℤ)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D)
    (hgrade : A d = (B d).comap e.toLinearMap) :
    residualPiece I D A d ≃ₗ[K] residualPiece J E B d where
  toFun H := ⟨e H.val,
    (residualIdeal_comap e I D J E hI hD).symm.le H.property.1,
    hgrade.le H.property.2⟩
  invFun H := ⟨e.symm H.val, by
    constructor
    · apply (residualIdeal_comap e I D J E hI hD).le
      change e (e.symm H.val) ∈ J.colon (E : Set S)
      rw [e.apply_symm_apply]
      exact H.property.1
    · apply hgrade.ge
      change e (e.symm H.val) ∈ B d
      rw [e.apply_symm_apply]
      exact H.property.2⟩
  left_inv H := by apply Subtype.ext; exact e.symm_apply_apply H.val
  right_inv H := by apply Subtype.ext; exact e.apply_symm_apply H.val
  map_add' H Q := by apply Subtype.ext; exact map_add e _ _
  map_smul' k H := by apply Subtype.ext; exact e.toLinearMap.map_smul k H.val

theorem equationPiece_map (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (A : ℤ → Submodule K R) (B : ℤ → Submodule K S) (d : ℤ)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D)
    (hgrade : A d = (B d).comap e.toLinearMap) :
    (equationPiece I D A d).map (residualPieceEquiv e I D J E A B d hI hD hgrade).toLinearMap =
      equationPiece J E B d := by
  apply le_antisymm
  · intro H hH
    obtain ⟨Q, hQ, rfl⟩ := hH
    exact hI.symm.le hQ
  · intro H hH
    refine ⟨(residualPieceEquiv e I D J E A B d hI hD hgrade).symm H, ?_,
      (residualPieceEquiv e I D J E A B d hI hD hgrade).apply_symm_apply H⟩
    apply hI.le
    change e (e.symm H.val) ∈ J
    rw [e.apply_symm_apply]
    exact hH

/-- The quotient equivalence is constructed from the actual coordinate
map and the proved transported ideals, rather than assumed. -/
def residualQuotientEquiv (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (A : ℤ → Submodule K R) (B : ℤ → Submodule K S) (d : ℤ)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D)
    (hgrade : A d = (B d).comap e.toLinearMap) :
    ResidualQuotient I D A d ≃ₗ[K] ResidualQuotient J E B d :=
  Submodule.Quotient.equiv _ _ (residualPieceEquiv e I D J E A B d hI hD hgrade)
    (equationPiece_map e I D J E A B d hI hD hgrade)

#print axioms comap_colon
#print axioms equationsIdeal_comap
#print axioms residualIdeal_comap
#print axioms residualQuotientEquiv

end Cylinder.ResidualCoordinateTransport

end
