module

public import Cylinder.CompleteIntersectionGraded

/-!
# The real plane complete-intersection Hilbert function

The exact degree-piece Koszul calculation gives dimension `e*t` in every
degree at least `e+t-2`, including the two boundary degrees with zero
relation spaces. The space is the homogeneous image in the actual ring
quotient, so nilpotents and intersection multiplicity remain present.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionHilbert

open Module MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.CompleteIntersectionKoszul Cylinder.CompleteIntersectionGraded
open scoped Classical

variable {K : Type*} [Field K]

theorem twice_forms_finrank (d : ℕ) :
    2 * finrank K (Forms K d) = (d + 1) * (d + 2) := by
  induction d with
  | zero => rw [forms_finrank_zero]
  | succ d ih =>
    rw [show d + 1 = d + 1 from rfl, forms_rank_succ]
    nlinarith

theorem twice_shiftedForms_finrank (e d : ℕ) :
    2 * finrank K (shiftedForms (K := K) e d) = (d + 1 - e) * (d + 2 - e) := by
  by_cases h : e ≤ d
  · rw [shiftedForms, if_pos h]
    have h1 : d - e + 1 = d + 1 - e := by omega
    have h2 : d - e + 2 = d + 2 - e := by omega
    simpa only [h1, h2] using twice_forms_finrank (K := K) (d - e)
  · rw [shiftedForms, if_neg h, finrank_bot]
    have h1 : d + 1 - e = 0 := by omega
    simp [h1]

private theorem dimension_arithmetic (q e t d : ℕ) (he : 0 < e) (ht : 0 < t)
    (hd : e + t - 2 ≤ d)
    (h : 2 * q + (d + 1 - e) * (d + 2 - e) + (d + 1 - t) * (d + 2 - t) =
      (d + 1) * (d + 2) + (d + 1 - (e + t)) * (d + 2 - (e + t))) : q = e * t := by
  by_cases hs : e + t ≤ d
  · have he1 : d + 1 - e + e = d + 1 := by omega
    have he2 : d + 2 - e = d + 1 - e + 1 := by omega
    have ht1 : d + 1 - t + t = d + 1 := by omega
    have ht2 : d + 2 - t = d + 1 - t + 1 := by omega
    have hs1 : d + 1 - (e + t) + e + t = d + 1 := by omega
    have hs2 : d + 2 - (e + t) = d + 1 - (e + t) + 1 := by omega
    nlinarith
  · by_cases hb : d + 1 = e + t
    · have he1 : d + 1 - e = t := by omega
      have he2 : d + 2 - e = t + 1 := by omega
      have ht1 : d + 1 - t = e := by omega
      have ht2 : d + 2 - t = e + 1 := by omega
      have hs1 : d + 1 - (e + t) = 0 := by omega
      rw [he1, he2, ht1, ht2, hs1, zero_mul, add_zero, hb] at h
      have hd2 : d + 2 = e + t + 1 := by omega
      rw [hd2] at h
      nlinarith
    · have hb2 : d + 2 = e + t := by omega
      have he1 : d + 1 - e = t - 1 := by omega
      have he2 : d + 2 - e = t := by omega
      have ht1 : d + 1 - t = e - 1 := by omega
      have ht2 : d + 2 - t = e := by omega
      have hs1 : d + 1 - (e + t) = 0 := by omega
      rw [he1, he2, ht1, ht2, hs1, zero_mul, add_zero, hb2] at h
      have he' : e - 1 + 1 = e := by omega
      have ht' : t - 1 + 1 = t := by omega
      nlinarith

/-- The degree-d homogeneous image in the actual quotient `K[X0,X1,X2]/(F,G)`
has dimension `e*t` throughout the stable range. -/
theorem quotientPiece_finrank (F G : PlaneRing K) (e t d : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hd : e + t - 2 ≤ d) :
    finrank K (quotientPiece F G d) = e * t := by
  have hr := quotientPiece_rank_formula F G e t d hF hG hF0 hcop
  have h := congrArg (fun n : ℕ => 2 * n) hr
  simp only [Nat.mul_add] at h
  rw [twice_shiftedForms_finrank, twice_shiftedForms_finrank,
    twice_forms_finrank, twice_shiftedForms_finrank] at h
  exact dimension_arithmetic _ e t d he ht hd h

/-- The equivalent quotient-of-forms API uses the actual degree ideal piece. -/
theorem forms_quotient_finrank (F G : PlaneRing K) (e t d : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hd : e + t - 2 ≤ d) :
    finrank K (Forms K d ⧸ idealPiece F G d) = e * t := by
  rw [← quotientPieceMap_kernel]
  rw [(quotientPieceMap F G d).quotKerEquivRange.finrank_eq]
  exact quotientPiece_finrank F G e t d he ht hF hG hF0 hcop hd

#print axioms quotientPiece_finrank
#print axioms forms_quotient_finrank

end Cylinder.CompleteIntersectionHilbert

end
