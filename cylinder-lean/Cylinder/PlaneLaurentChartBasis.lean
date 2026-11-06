module

public import Cylinder.PlaneLaurentPieces
public import Mathlib.Algebra.MvPolynomial.Basic

/-! The coordinate-chart Laurent piece in degree v has the actual
polynomial monomial basis in the other two coordinates. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentChartBasis

open Cylinder.PlaneLaurentPieces MvPolynomial

set_option autoImplicit false

def exponentOf (v : ℤ) (m : Fin 2 →₀ ℕ) : Exponent :=
  Fin.cases (v - (m 0 : ℤ) - m 1) (fun i => (m i : ℤ))

theorem exponentOf_allowed (v : ℤ) (m : Fin 2 →₀ ℕ) : Allowed v {0} (exponentOf v m) := by
  constructor
  · change v - (m 0 : ℤ) - m 1 + m 0 + m 1 = v
    omega
  · intro i hi
    fin_cases i
    · simp at hi
    · change 0 ≤ (m 0 : ℤ)
      exact Int.natCast_nonneg _
    · change 0 ≤ (m 1 : ℤ)
      exact Int.natCast_nonneg _

def exponentEquiv (v : ℤ) : {a : Exponent // Allowed v {0} a} ≃ (Fin 2 →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm (fun i => (a.val i.succ).toNat)
  invFun m := ⟨exponentOf v m, exponentOf_allowed v m⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    have h₁ : 0 ≤ a.val 1 := a.property.2 1 (by simp)
    have h₂ : 0 ≤ a.val 2 := a.property.2 2 (by simp)
    have hd : totalDegree a.val = v := a.property.1
    fin_cases i
    · change v - ((a.val 1).toNat : ℤ) - (a.val 2).toNat = a.val 0
      rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
      dsimp [totalDegree] at hd
      omega
    · change ((a.val 1).toNat : ℤ) = a.val 1
      exact Int.toNat_of_nonneg h₁
    · change ((a.val 2).toNat : ℤ) = a.val 2
      exact Int.toNat_of_nonneg h₂
  right_inv m := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · change (m 0 : ℤ).toNat = m 0
      exact Int.toNat_natCast _
    · change (m 1 : ℤ).toNat = m 1
      exact Int.toNat_natCast _

variable {K : Type*} [CommRing K]

def chartPolynomialEquiv (v : ℤ) : piece (K := K) v {0} ≃ₗ[K] MvPolynomial (Fin 2) K :=
  (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v {0} a}).trans
    ((Finsupp.domLCongr (exponentEquiv v)).trans
      (AddMonoidAlgebra.coeffLinearEquiv K).symm)

end Cylinder.PlaneLaurentChartBasis

end
