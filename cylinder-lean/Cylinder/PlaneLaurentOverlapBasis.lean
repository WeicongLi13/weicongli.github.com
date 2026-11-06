module

public import Cylinder.PlaneLaurentChartBasis
public import Mathlib.Algebra.Polynomial.Laurent

/-! The double-coordinate Laurent piece has the genuine Laurent
polynomial basis in the affine ratio X1/X0, with polynomial
coefficients in X2/X0. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentOverlapBasis

open Cylinder.PlaneLaurentPieces MvPolynomial

set_option autoImplicit false

abbrev overlapRing (K : Type*) [CommRing K] := LaurentPolynomial (MvPolynomial (Fin 1) K)

def exponentOf (v : ℤ) (dm : ℤ × (Fin 1 →₀ ℕ)) : Exponent :=
  ![v - dm.1 - (dm.2 0 : ℤ), dm.1, dm.2 0]

theorem exponentOf_allowed (v : ℤ) (dm : ℤ × (Fin 1 →₀ ℕ)) :
    Allowed v {0, 1} (exponentOf v dm) := by
  constructor
  · change v - dm.1 - (dm.2 0 : ℤ) + dm.1 + dm.2 0 = v
    omega
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · change 0 ≤ (dm.2 0 : ℤ)
      exact Int.natCast_nonneg _

def exponentEquiv (v : ℤ) :
    {a : Exponent // Allowed v {0, 1} a} ≃ ℤ × (Fin 1 →₀ ℕ) where
  toFun a := (a.val 1, Finsupp.single 0 (a.val 2).toNat)
  invFun dm := ⟨exponentOf v dm, exponentOf_allowed v dm⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    have h₂ : 0 ≤ a.val 2 := a.property.2 2 (by simp)
    have hd : totalDegree a.val = v := a.property.1
    fin_cases i
    · change v - a.val 1 - ((Finsupp.single 0 (a.val 2).toNat : Fin 1 →₀ ℕ) 0 : ℤ) = a.val 0
      simp only [Finsupp.single_eq_same, Int.toNat_of_nonneg h₂]
      dsimp [totalDegree] at hd
      omega
    · rfl
    · change ((Finsupp.single 0 (a.val 2).toNat : Fin 1 →₀ ℕ) 0 : ℤ) = a.val 2
      simp only [Finsupp.single_eq_same, Int.toNat_of_nonneg h₂]
  right_inv dm := by
    apply Prod.ext
    · rfl
    · apply Finsupp.ext
      intro i
      fin_cases i
      change (Finsupp.single 0 (dm.2 0 : ℤ).toNat : Fin 1 →₀ ℕ) 0 = dm.2 0
      simp

variable {K : Type*} [CommRing K]

def overlapLaurentEquiv (v : ℤ) : piece (K := K) v {0, 1} ≃ₗ[K] overlapRing K :=
  (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v {0, 1} a}).trans
    ((Finsupp.domLCongr (exponentEquiv v)).trans
      ((Finsupp.curryLinearEquiv K).trans
        ((Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv K).symm).trans
          (AddMonoidAlgebra.coeffLinearEquiv K).symm)))

theorem overlapLaurentEquiv_coeff (v : ℤ) (s : piece (K := K) v {0, 1})
    (d : ℤ) (m : Fin 1 →₀ ℕ) :
    ((overlapLaurentEquiv v s).coeff d).coeff m = s.val (exponentOf v (d, m)) := by
  rfl

end Cylinder.PlaneLaurentOverlapBasis

end
