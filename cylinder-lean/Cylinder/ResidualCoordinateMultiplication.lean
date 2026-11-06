module

public import Cylinder.ResidualCoordinateTransport

/-! Genuine polynomial multiplication on residual quotient pieces,
and its compatibility with the genuine coordinate quotient equivalence. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualCoordinateMultiplication

open Module Cylinder.ResidualCoordinateTransport
open scoped Classical

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

def residualPieceMultiplication (I D : Ideal R) (A : ℤ → Submodule K R) (d m : ℤ)
    (Q : R) (hprod : ∀ H ∈ A d, Q * H ∈ A m) :
    residualPiece I D A d →ₗ[K] residualPiece I D A m where
  toFun H := ⟨Q * H.val, (I.colon (D : Set R)).mul_mem_left Q H.property.1,
    hprod H.val H.property.2⟩
  map_add' H H' := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' k H := by apply Subtype.ext; exact mul_smul_comm _ _ _

/-- Actual multiplication by Q on actual quotient representatives. -/
def residualMultiplication (I D : Ideal R) (A : ℤ → Submodule K R) (d m : ℤ)
    (Q : R) (hprod : ∀ H ∈ A d, Q * H ∈ A m) :
    ResidualQuotient I D A d →ₗ[K] ResidualQuotient I D A m :=
  Submodule.mapQ (R := K) (R₂ := K) (τ₁₂ := RingHom.id K)
    (equationPiece I D A d) (equationPiece I D A m)
    (residualPieceMultiplication I D A d m Q hprod) (by
      intro H hH
      exact I.mul_mem_left Q hH)

theorem residualMultiplication_apply_mk (I D : Ideal R) (A : ℤ → Submodule K R) (d m : ℤ)
    (Q : R) (hprod : ∀ H ∈ A d, Q * H ∈ A m) (H : residualPiece I D A d) :
    residualMultiplication I D A d m Q hprod (Submodule.Quotient.mk H) =
      Submodule.Quotient.mk (residualPieceMultiplication I D A d m Q hprod H) := rfl

theorem coordinateQuotientEquiv_apply_mk (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (A : ℤ → Submodule K R) (B : ℤ → Submodule K S) (d : ℤ)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D)
    (hgrade : A d = (B d).comap e.toLinearMap) (H : residualPiece I D A d) :
    residualQuotientEquiv e I D J E A B d hI hD hgrade (Submodule.Quotient.mk H) =
      Submodule.Quotient.mk (residualPieceEquiv e I D J E A B d hI hD hgrade H) := rfl

/-- The actual coordinate isomorphism commutes with polynomial
multiplication. The only multiplication inputs express degree closure. -/
theorem coordinateQuotientEquiv_multiply (e : R ≃ₐ[K] S) (I D : Ideal R) (J E : Ideal S)
    (A : ℤ → Submodule K R) (B : ℤ → Submodule K S) (d m : ℤ)
    (hI : Ideal.comap e J = I) (hD : Ideal.comap e E = D)
    (hgradeD : A d = (B d).comap e.toLinearMap)
    (hgradeM : A m = (B m).comap e.toLinearMap)
    (Q : R) (hprodSource : ∀ H ∈ A d, Q * H ∈ A m)
    (hprodTarget : ∀ H ∈ B d, e Q * H ∈ B m) (a : ResidualQuotient I D A d) :
    residualQuotientEquiv e I D J E A B m hI hD hgradeM
      (residualMultiplication I D A d m Q hprodSource a) =
    residualMultiplication J E B d m (e Q) hprodTarget
      (residualQuotientEquiv e I D J E A B d hI hD hgradeD a) := by
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (equationPiece I D A d) a
  rw [residualMultiplication_apply_mk, coordinateQuotientEquiv_apply_mk,
    coordinateQuotientEquiv_apply_mk, residualMultiplication_apply_mk]
  congr 1
  apply Subtype.ext
  exact map_mul e Q H.val

#print axioms residualMultiplication
#print axioms residualMultiplication_apply_mk
#print axioms coordinateQuotientEquiv_apply_mk
#print axioms coordinateQuotientEquiv_multiply

end Cylinder.ResidualCoordinateMultiplication

end
