module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Division of homogeneous polynomials

The graded decomposition of the actual three-variable polynomial ring
shows that cancelling a nonzero homogeneous denominator leaves the
required homogeneous component of the quotient. The proof also covers
a zero numerator, for which cancellation forces the quotient to be zero.
-/

@[expose] public section

namespace Cylinder.HomogeneousDivision

variable {K : Type*} [Field K]

/-- A polynomial quotient of homogeneous polynomials has the difference
of their degrees. No assumption that the numerator is nonzero is needed. -/
theorem quotient_isHomogeneous
    (A N F : MvPolynomial (Fin 3) K) (r d : ℕ)
    (hA0 : A ≠ 0) (hA : A.IsHomogeneous r)
    (hN : N.IsHomogeneous (r + d)) (hAF : A * F = N) :
    F.IsHomogeneous d := by
  let := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := K)
  let H := MvPolynomial.homogeneousSubmodule (Fin 3) K
  have hprod := DirectSum.coe_decompose_mul_add_of_left_mem H
    (i := r) (j := d) (a := A) (b := F) hA
  rw [hAF, DirectSum.decompose_of_mem_same H hN] at hprod
  have hcomponent : F = (DirectSum.decompose H F d : MvPolynomial (Fin 3) K) :=
    mul_left_cancel₀ hA0 (hAF.trans hprod)
  have hh : (DirectSum.decompose H F d : MvPolynomial (Fin 3) K) ∈ H d :=
    (DirectSum.decompose H F d).property
  exact hcomponent.symm ▸ hh

end Cylinder.HomogeneousDivision
