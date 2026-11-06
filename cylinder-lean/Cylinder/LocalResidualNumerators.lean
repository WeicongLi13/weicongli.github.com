module

public import Cylinder.PlanePlateauTheorem
public import Cylinder.HomogeneousDivision
public import Cylinder.LocalCurveInterpolation

/-! The genuine saturated residual-ideal plateau constructs the common
factor and homogeneous numerator family used in local interpolation. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalResidualNumerators

open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.SaturatedPlaneLine
open Cylinder.NumericCharacterSequence Cylinder.PlanePlateauTheorem
open Cylinder.HomogeneousDivision Cylinder.LocalCurveInterpolation
open scoped Classical

variable {K : Type*} [Field K] [Infinite K]

theorem initial_degree_of_equation (J : Ideal (PlaneRing K)) (Q : PlaneRing K) (β : ℕ)
    (hQ : Q.IsHomogeneous β) (hQJ : Q ∈ J) (hQ0 : Q ≠ 0) :
    ∃ z ≤ β, Cylinder.PlanePlateau.InitialDegree J z := by
  have hβ : Cylinder.PlanePlateau.piece J β ≠ ⊥ := by
    intro hz
    have hmem : Q ∈ Cylinder.PlanePlateau.piece J β := ⟨hQJ, hQ⟩
    rw [hz, Submodule.mem_bot] at hmem
    exact hQ0 hmem
  have hex : ∃ z, Cylinder.PlanePlateau.piece J z ≠ ⊥ := ⟨β, hβ⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hβ, Nat.find_spec hex, ?_⟩
  intro d hd
  exact not_not.mp (Nat.find_min hex hd)

/-- Actual Hilbert first differences and a genuine nonzero residual
equation construct the common factor. The factor is not an input. -/
theorem common_numerators (J : Ideal (PlaneRing K)) (hJ : Saturated J) (β m : ℕ)
    (hmβ : m ≤ β) (Q : ℕ → PlaneRing K)
    (hQhom : ∀ v ≤ 2 * m + 2, (Q v).IsHomogeneous (β + v))
    (hQJ : ∀ v ≤ 2 * m + 2, Q v ∈ J) (hQ0 : Q 0 ≠ 0)
    (h0 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (β + 2 * m + 1) = β - m)
    (h1 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (β + 2 * m + 2) = β - m) :
    ∃ K₀ A : PlaneRing K, ∃ num : ℕ → PlaneRing K,
      K₀ ≠ 0 ∧ K₀.IsHomogeneous (β - m) ∧ A ≠ 0 ∧ A.IsHomogeneous m ∧
      Q 0 = K₀ * A ∧ num 0 = A ∧
      ∀ v ≤ 2 * m + 2, (num v).IsHomogeneous (m + v) ∧ Q v = K₀ * num v := by
  by_cases hβm : β = m
  · refine ⟨1, Q 0, Q, one_ne_zero,
      by simpa only [hβm, Nat.sub_self] using isHomogeneous_one (Fin 3) K, hQ0, ?_, by simp, rfl, ?_⟩
    · simpa only [hβm, Nat.add_zero] using hQhom 0 (by omega)
    · intro v hv
      exact ⟨by simpa only [hβm] using hQhom v hv, by simp⟩
  · have hmβ' : m < β := by omega
    obtain ⟨z, hzβ, hz⟩ := initial_degree_of_equation J (Q 0) β
      (by simpa only [Nat.add_zero] using hQhom 0 (by omega)) (hQJ 0 (by omega)) hQ0
    obtain ⟨K₀, hK0, hK, hKdeg, hdiv⟩ := plane_plateau J hJ z (β + 2 * m + 1) (β - m)
      hz (by omega) (by omega) h0 (by simpa only [Nat.add_assoc] using h1)
    have hquot : ∀ v ≤ 2 * m + 2, ∃ N : PlaneRing K,
        N.IsHomogeneous (m + v) ∧ Q v = K₀ * N := by
      intro v hv
      obtain ⟨N, hN⟩ := hdiv (β + v) (Q v) (hQhom v hv) (hQJ v hv) (by omega)
      have heq : β - m + (m + v) = β + v := by omega
      have hhom := quotient_isHomogeneous K₀ (Q v) N (β - m) (m + v) hK0 hK
        (by simpa only [heq] using hQhom v hv) hN.symm
      exact ⟨N, hhom, hN⟩
    let num (v : ℕ) : PlaneRing K := if hv : v ≤ 2 * m + 2 then (hquot v hv).choose else 0
    have hnum : ∀ v ≤ 2 * m + 2, (num v).IsHomogeneous (m + v) ∧ Q v = K₀ * num v := by
      intro v hv
      simpa only [num, dif_pos hv] using (hquot v hv).choose_spec
    have hA0 : num 0 ≠ 0 := by
      intro hz0
      exact hQ0 (by simpa only [hz0, mul_zero] using (hnum 0 (by omega)).2)
    refine ⟨K₀, num 0, num, hK0, hK, hA0, ?_, (hnum 0 (by omega)).2, rfl, hnum⟩
    simpa only [Nat.add_zero] using (hnum 0 (by omega)).1

#print axioms initial_degree_of_equation
#print axioms common_numerators

end Cylinder.LocalResidualNumerators

end
