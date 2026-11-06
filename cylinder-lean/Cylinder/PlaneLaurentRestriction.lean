module

public import Cylinder.PlaneLaurentOverlapBasis
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! Polynomial restriction to the double-coordinate Laurent chart
is exactly the inclusion of the homogeneous Laurent pieces. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentRestriction

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentChartBasis
open Cylinder.PlaneLaurentOverlapBasis MvPolynomial

set_option autoImplicit false

variable {K : Type*} [CommRing K]

def chartInclusion (v : ℤ) : piece (K := K) v {0} →ₗ[K] piece (K := K) v {0, 1} :=
  Submodule.inclusion (p := piece (K := K) v {0}) (p' := piece (K := K) v {0, 1})
    (piece_mono (K := K) v (by simp))

theorem toLaurent_coeff_nat {R : Type*} [CommRing R] (p : Polynomial R) (n : ℕ) :
    (Polynomial.toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

theorem toLaurent_coeff_negative {R : Type*} [CommRing R] (p : Polynomial R)
    (d : ℤ) (hd : d < 0) : (Polynomial.toLaurent p).coeff d = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n, hn⟩
  change (n : ℤ) = d at hn
  omega

theorem chart_restriction (v : ℤ) (s : piece (K := K) v {0}) :
    overlapLaurentEquiv v (chartInclusion v s) =
      Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 (chartPolynomialEquiv v s)) := by
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro d
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro m
  change ((overlapLaurentEquiv v (chartInclusion v s)).coeff d).coeff m =
    ((Polynomial.toLaurent (MvPolynomial.finSuccEquiv K 1 (chartPolynomialEquiv v s))).coeff d).coeff m
  rw [overlapLaurentEquiv_coeff]
  by_cases hd : 0 ≤ d
  · rw [← Int.toNat_of_nonneg hd, toLaurent_coeff_nat, finSuccEquiv_coeff_coeff]
    change s.val (PlaneLaurentOverlapBasis.exponentOf v ((d.toNat : ℤ), m)) =
      s.val (PlaneLaurentChartBasis.exponentOf v (m.cons d.toNat))
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [toLaurent_coeff_negative _ d (by omega)]
    change s.val (PlaneLaurentOverlapBasis.exponentOf v (d, m)) = 0
    apply coeff_zero_of_negative s.property _ 1 (by simp)
    change d < 0
    omega

end Cylinder.PlaneLaurentRestriction

end
