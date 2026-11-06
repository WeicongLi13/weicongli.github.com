module

public import Cylinder.CoordinateTwistFractions
public import Cylinder.PlaneLaurentChartBasis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A genuine degree-v module of homogeneous fractions in the coordinate
localization is linearly equivalent to the standard Laurent chart piece.
The proof uses actual monomial normal forms, not a stipulated equivalence
with twisting-sheaf sections. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CoordinateTwistLaurentPiece

open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistFractions
open Cylinder.PlaneLaurentChartBasis Cylinder.PlaneLaurentPieces MvPolynomial

set_option autoImplicit false

variable (K : Type*) [CommRing K]

def coefficientAlgHom : AffineRing K →ₐ[K] LaurentChart K where
  __ := LaurentPolynomial.C
  commutes' _ := rfl

def evaluateOneAlgHom : LaurentChart K →ₐ[K] AffineRing K where
  __ := LaurentPolynomial.eval₂ (RingHom.id (AffineRing K)) 1
  commutes' a := by
    change LaurentPolynomial.eval₂ (RingHom.id (AffineRing K)) 1
      (LaurentPolynomial.C (MvPolynomial.C a)) = MvPolynomial.C a
    simp

def affineLift (v : ℤ) : AffineRing K →ₗ[K] LaurentChart K :=
  (Finsupp.linearCombination K (fun m : Fin 2 →₀ ℕ =>
    LaurentPolynomial.C (MvPolynomial.monomial m (1 : K)) *
      LaurentPolynomial.T (v - m.degree))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem affineLift_monomial (v : ℤ) (m : Fin 2 →₀ ℕ) (a : K) :
    affineLift K v (MvPolynomial.monomial m a) =
      LaurentPolynomial.C (MvPolynomial.monomial m a) * LaurentPolynomial.T (v - m.degree) := by
  change Finsupp.linearCombination K _ (Finsupp.single m a) = _
  rw [Finsupp.linearCombination_single, ← smul_mul_assoc]
  congr 1
  change a • coefficientAlgHom K (MvPolynomial.monomial m 1) =
    coefficientAlgHom K (MvPolynomial.monomial m a)
  rw [← map_smul]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem evaluateOne_affineLift (v : ℤ) :
    Function.LeftInverse (evaluateOneAlgHom K) (affineLift K v) := by
  intro f
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [affineLift_monomial]
      change LaurentPolynomial.eval₂ (RingHom.id (AffineRing K)) 1
        (LaurentPolynomial.C (MvPolynomial.monomial m a) * LaurentPolynomial.T _) = _
      simp
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]

theorem affineLift_injective (v : ℤ) : Function.Injective (affineLift K v) :=
  (evaluateOne_affineLift K v).injective

theorem range_affineLift (v : ℤ) : LinearMap.range (affineLift K v) = weightedLaurentPiece K v := by
  apply le_antisymm
  · rintro z ⟨p, rfl⟩
    rw [p.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    rw [affineLift_monomial]
    apply Submodule.subset_span
    exact ⟨m, v - m.degree, p.coeff m, by omega, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨m, d, a, hd, rfl⟩
    refine ⟨MvPolynomial.monomial m a, ?_⟩
    rw [affineLift_monomial]
    have he : v - (m.degree : ℤ) = d := by omega
    rw [he]

def affineWeightedEquiv (v : ℤ) : AffineRing K ≃ₗ[K] weightedLaurentPiece K v :=
  (LinearEquiv.ofInjective (affineLift K v) (affineLift_injective K v)).trans
    (LinearEquiv.ofEq _ _ (range_affineLift K v))

/-- The actual homogeneous-fraction module equals the coordinate
Laurent model in every integer degree. No projective sheaf-section
identification or cohomological comparison is assumed here. -/
def localTwistLaurentEquiv (v : ℤ) :
    twistPiece K v ≃ₗ[K] piece (K := K) v {0} :=
  (twistLaurentEquiv K v).trans
    ((affineWeightedEquiv K v).symm.trans (chartPolynomialEquiv (K := K) v).symm)

end Cylinder.CoordinateTwistLaurentPiece

end
