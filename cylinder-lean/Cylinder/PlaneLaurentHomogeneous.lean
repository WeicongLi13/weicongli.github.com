module

public import Cylinder.PlaneLaurentH0
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The Laurent piece without poles is the actual space of homogeneous
polynomials. In negative integer degree this is the zero submodule. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

namespace Cylinder.PlaneLaurentHomogeneous

open MvPolynomial Cylinder.PlaneLaurentPieces

abbrev Monomial := Option (Fin 2) →₀ ℕ

def monomialExponent (m : Monomial) : Exponent :=
  Fin.cases (m none : ℤ) (fun i => (m (some i) : ℤ))

def naturalExponent (a : Exponent) : Monomial :=
  Finsupp.equivFunOnFinite.symm (fun i => i.elim (a 0).toNat (fun j => (a j.succ).toNat))

theorem monomialExponent_degree (m : Monomial) :
    totalDegree (monomialExponent m) = (m.degree : ℤ) := by
  change (m none : ℤ) + (m (some 0) : ℤ) + (m (some 1) : ℤ) = _
  simp [Finsupp.degree_eq_sum, Fintype.sum_option, Fin.sum_univ_two, add_assoc]

theorem monomialExponent_nonnegative (m : Monomial) (i : Fin 3) :
    0 ≤ monomialExponent m i := by
  fin_cases i <;> exact Int.natCast_nonneg _

theorem monomialExponent_naturalExponent (a : Exponent) (ha : ∀ i, 0 ≤ a i) :
    monomialExponent (naturalExponent a) = a := by
  funext i
  fin_cases i <;> exact Int.toNat_of_nonneg (ha _)

theorem naturalExponent_monomialExponent (m : Monomial) :
    naturalExponent (monomialExponent m) = m := by
  apply Finsupp.ext
  intro i
  cases i with
  | none => exact Int.toNat_natCast _
  | some j =>
    fin_cases j <;> exact Int.toNat_natCast _

def exponentEquiv (v : ℤ) :
    {a : Exponent // Allowed v ∅ a} ≃ {m : Monomial // (m.degree : ℤ) = v} where
  toFun a := ⟨naturalExponent a.val, by
    calc
      _ = totalDegree (monomialExponent (naturalExponent a.val)) :=
        (monomialExponent_degree _).symm
      _ = totalDegree a.val := congrArg totalDegree
        (monomialExponent_naturalExponent a.val (fun i => a.property.2 i (by simp)))
      _ = v := a.property.1⟩
  invFun m := ⟨monomialExponent m.val,
    (monomialExponent_degree m.val).trans m.property, fun i _ => monomialExponent_nonnegative m.val i⟩
  left_inv a := Subtype.ext
    (monomialExponent_naturalExponent a.val (fun i => a.property.2 i (by simp)))
  right_inv m := Subtype.ext (naturalExponent_monomialExponent m.val)

variable (K : Type*) [CommRing K]

def polynomialPiece (v : ℤ) : Submodule K (MvPolynomial (Option (Fin 2)) K) :=
  AddMonoidAlgebra.supported K K {m : Monomial | (m.degree : ℤ) = v}

def integerForms (v : ℤ) : Submodule K (MvPolynomial (Option (Fin 2)) K) :=
  if 0 ≤ v then homogeneousSubmodule (Option (Fin 2)) K v.toNat else ⊥

theorem polynomialPiece_eq_integerForms (v : ℤ) : polynomialPiece K v = integerForms K v := by
  by_cases hv : 0 ≤ v
  · rw [integerForms, ite_eq_left hv, homogeneousSubmodule_eq_finsupp_supported, polynomialPiece]
    apply congrArg (AddMonoidAlgebra.supported K K)
    ext m
    change (m.degree : ℤ) = v ↔ m.degree = v.toNat
    have hcast := Int.toNat_of_nonneg hv
    omega
  · rw [integerForms, ite_eq_right hv]
    apply le_antisymm
    · intro H hH
      change H = 0
      change (↑H.support : Set Monomial) ⊆ {m : Monomial | (m.degree : ℤ) = v} at hH
      ext m
      by_contra hm
      have he := hH (Finsupp.mem_support_iff.mpr hm)
      have hn := Int.natCast_nonneg m.degree
      change (m.degree : ℤ) = v at he
      omega
    · exact bot_le

def globalPieceEquivPolynomial (v : ℤ) : piece (K := K) v ∅ ≃ₗ[K] polynomialPiece K v :=
  (Finsupp.supportedEquivFinsupp (M := K) (R := K) {a | Allowed v ∅ a}).trans
    ((Finsupp.domLCongr (exponentEquiv v)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
        {m : Monomial | (m.degree : ℤ) = v}).symm)

def globalPieceEquivForms (v : ℤ) : piece (K := K) v ∅ ≃ₗ[K] integerForms K v :=
  (globalPieceEquivPolynomial K v).trans
    (LinearEquiv.ofEq _ _ (polynomialPiece_eq_integerForms K v))

def kernelEquivForms (v : ℤ) :
    LinearMap.ker (PlaneLaurentCech.differentialZero (K := K) v) ≃ₗ[K] integerForms K v :=
  (PlaneLaurentH0.globalPieceEquivKernel v).symm.trans (globalPieceEquivForms K v)

end Cylinder.PlaneLaurentHomogeneous
end
