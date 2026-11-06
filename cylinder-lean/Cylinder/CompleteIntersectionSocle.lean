module

public import Cylinder.BinaryCompleteIntersectionGraded

/-!
# The actual homogeneous binary complete-intersection socle

The Koszul relation for the two equations is applied to the cross relation
coming from multiplication by the two variables. Below `e+t-2` the cross
coefficient has negative shifted degree, so it vanishes. Cancellation then
proves that a homogeneous socle class below the top degree is zero.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionSocle

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded
open scoped Classical

variable {K : Type*} [Field K]

theorem shiftedForms_X_mul (r d : ℕ) (i : Fin 2)
    (P : shiftedForms (K := K) r d) :
    X i * P.val ∈ shiftedForms (K := K) r (d + 1) := by
  apply (mem_shiftedForms _ _ _).mpr
  by_cases hr : r ≤ d
  · have hr' : r ≤ d + 1 := by omega
    simp only [hr', ite_true]
    have hh := (isHomogeneous_X K i).mul (shiftedForms_homogeneous r d P)
    convert hh using 1 <;> omega
  · rw [shiftedForms_zero_of_not_le r d P hr, mul_zero]
    split <;> simp [isHomogeneous_zero]

/-- A homogeneous class killed by both variables below the socle degree is
zero in the actual quotient. -/
theorem homogeneous_socle_below (F G : BinaryRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (P : BinaryRing K) (hP : P.IsHomogeneous d) (hd : d < e + t - 2)
    (hXP : X (0 : Fin 2) * P ∈ equationsIdeal F G)
    (hYP : X (1 : Fin 2) * P ∈ equationsIdeal F G) :
    P ∈ equationsIdeal F G := by
  let XP : BinaryForms K (d + 1) := ⟨X 0 * P, by
    simpa [Nat.add_comm] using (isHomogeneous_X K (0 : Fin 2)).mul hP⟩
  let YP : BinaryForms K (d + 1) := ⟨X 1 * P, by
    simpa [Nat.add_comm] using (isHomogeneous_X K (1 : Fin 2)).mul hP⟩
  have hX : XP ∈ LinearMap.range (gradedGenerator F G e t (d + 1) hF hG) := by
    rw [gradedGenerator_range]; exact hXP
  have hY : YP ∈ LinearMap.range (gradedGenerator F G e t (d + 1) hF hG) := by
    rw [gradedGenerator_range]; exact hYP
  obtain ⟨A, hA⟩ := hX
  obtain ⟨B, hB⟩ := hY
  have hAe : A.1.val * F + A.2.val * G = X 0 * P := congrArg Subtype.val hA
  have hBe : B.1.val * F + B.2.val * G = X 1 * P := congrArg Subtype.val hB
  let C : BinaryRing K := X 1 * A.1.val - X 0 * B.1.val
  let D : BinaryRing K := X 1 * A.2.val - X 0 * B.2.val
  have hCD : C * F + D * G = 0 := by
    dsimp [C, D]
    calc
      _ = X 1 * (A.1.val * F + A.2.val * G) -
        X 0 * (B.1.val * F + B.2.val * G) := by ring
      _ = 0 := by rw [hAe, hBe]; ring
  obtain ⟨c, hC, hD⟩ := (koszul_syzygy_iff F G hF0 hcop C D).mp hCD
  have hDm : D ∈ shiftedForms (K := K) t (d + 2) := by
    exact (shiftedForms (K := K) t (d + 2)).sub_mem
      (by simpa [Nat.add_assoc] using shiftedForms_X_mul t (d + 1) 1 A.2)
      (by simpa [Nat.add_assoc] using shiftedForms_X_mul t (d + 1) 0 B.2)
  have hc := koszul_coefficient_mem F G D c e t (d + 2) hF hF0 hDm hD
  have hc0 : c = 0 := by
    have hs : ¬e + t ≤ d + 2 := by omega
    simpa only [hs, ite_false] using (mem_shiftedForms (e + t) (d + 2) c).mp hc
  have hC0 : X 1 * A.1.val = X 0 * B.1.val := by
    have h := hC
    rw [hc0, mul_zero] at h
    exact sub_eq_zero.mp h
  have hD0 : X 1 * A.2.val = X 0 * B.2.val := by
    have h := hD
    rw [hc0, mul_zero] at h
    exact sub_eq_zero.mp h
  have hdiv (Q R : BinaryRing K) (h : X 1 * Q = X 0 * R) : X (0 : Fin 2) ∣ Q := by
    have hx : X (0 : Fin 2) ∣ X 1 * Q := by rw [h]; exact dvd_mul_right _ _
    apply (X_dvd_mul_iff.mp hx).resolve_left
    intro hh
    have h01 := X_dvd_X.mp hh
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  obtain ⟨U, hU⟩ := hdiv A.1.val B.1.val hC0
  obtain ⟨V, hV⟩ := hdiv A.2.val B.2.val hD0
  apply Ideal.mem_span_pair.mpr
  refine ⟨U, V, ?_⟩
  apply mul_left_cancel₀ (X_ne_zero (0 : Fin 2))
  calc
    X 0 * (U * F + V * G) = A.1.val * F + A.2.val * G := by rw [hU, hV]; ring
    _ = X 0 * P := hAe

theorem homogeneous_high_mem_ideal (F G : BinaryRing K) (e t d : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (P : BinaryRing K) (hP : P.IsHomogeneous d)
    (hd : e + t - 1 ≤ d) : P ∈ equationsIdeal F G := by
  rw [← support_sum_monomial_coeff P]
  apply Ideal.sum_mem
  intro α hα
  apply CompleteIntersectionFinite.high_monomial_mem_ideal F G e t he ht hF hG hF0 hG0 hcop
  have hdeg : α.degree = d := (hP.degree_eq_sum_deg_support hα).symm
  exact hd.trans_eq hdeg.symm

theorem shiftedForms_finrank (e d : ℕ) :
    finrank K (shiftedForms (K := K) e d) = d + 1 - e := by
  by_cases he : e ≤ d
  · rw [shiftedForms, if_pos he, binaryForms_finrank]
    omega
  · rw [shiftedForms, if_neg he, finrank_bot]
    omega

/-- The genuine top homogeneous quotient piece is one dimensional. -/
theorem top_quotientPiece_finrank (F G : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    finrank K (quotientPiece F G (e + t - 2)) = 1 := by
  have h := quotientPiece_rank_formula F G e t (e + t - 2) hF hG hF0 hcop
  rw [shiftedForms_finrank, shiftedForms_finrank, binaryForms_finrank,
    shiftedForms_finrank] at h
  omega

#print axioms homogeneous_socle_below
#print axioms homogeneous_high_mem_ideal
#print axioms top_quotientPiece_finrank

end Cylinder.CompleteIntersectionSocle

end

