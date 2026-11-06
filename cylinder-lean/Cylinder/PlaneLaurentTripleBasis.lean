module

public import Cylinder.PlaneLaurentOverlapBasis

/-! The triple-coordinate homogeneous Laurent piece is the true
iterated Laurent polynomial ring, via its two free integer exponents. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentTripleBasis

open Cylinder.PlaneLaurentPieces

set_option autoImplicit false

abbrev tripleRing (K : Type*) [CommRing K] := LaurentPolynomial (LaurentPolynomial K)

def exponentOf (v : ℤ) (dm : ℤ × ℤ) : Exponent := ![v - dm.1 - dm.2, dm.1, dm.2]

theorem exponentOf_allowed (v : ℤ) (dm : ℤ × ℤ) :
    Allowed v {0, 1, 2} (exponentOf v dm) := by
  constructor
  · change v - dm.1 - dm.2 + dm.1 + dm.2 = v
    omega
  · intro i hi
    fin_cases i <;> simp at hi

def exponentEquiv (v : ℤ) :
    {a : Exponent // Allowed v {0, 1, 2} a} ≃ ℤ × ℤ where
  toFun a := (a.val 1, a.val 2)
  invFun dm := ⟨exponentOf v dm, exponentOf_allowed v dm⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    have hd : a.val 0 + a.val 1 + a.val 2 = v := a.property.1
    fin_cases i
    · change v - a.val 1 - a.val 2 = a.val 0
      omega
    · rfl
    · rfl
  right_inv dm := rfl

variable {K : Type*} [CommRing K]

def tripleLaurentEquiv (v : ℤ) : piece (K := K) v {0, 1, 2} ≃ₗ[K] tripleRing K :=
  (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v {0, 1, 2} a}).trans
    ((Finsupp.domLCongr (exponentEquiv v)).trans
      ((Finsupp.curryLinearEquiv K).trans
        ((Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv K).symm).trans
          (AddMonoidAlgebra.coeffLinearEquiv K).symm)))

theorem tripleLaurentEquiv_coeff (v : ℤ) (s : piece (K := K) v {0, 1, 2})
    (d m : ℤ) :
    ((tripleLaurentEquiv v s).coeff d).coeff m = s.val (exponentOf v (d, m)) := rfl

end Cylinder.PlaneLaurentTripleBasis

end
