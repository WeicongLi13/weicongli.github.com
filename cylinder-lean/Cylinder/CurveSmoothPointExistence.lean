module

public import Cylinder.FrobeniusLowDegree
public import Cylinder.CurveTangentRestriction
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# A genuine smooth affine point on a low-degree irreducible curve

Nonzero partial derivatives have smaller total degree. The
Nullstellensatz then produces a zero of the irreducible equation at
which a chosen nonzero partial derivative does not vanish. Existence
of a smooth point is proved and is not an extra geometric hypothesis.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurveSmoothPointExistence

open MvPolynomial Finsupp Cylinder.CurveLocalParameter
open scoped Classical

variable {K : Type*} [Field K]

theorem pderiv_totalDegree_lt (F : PlanePolynomial (K := K)) (i : Fin 2)
    (hderiv : pderiv i F ≠ 0) : (pderiv i F).totalDegree < F.totalDegree := by
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr hderiv)
    (fun m : Fin 2 →₀ ℕ => m.sum fun _ n => n)
  change (pderiv i F).totalDegree = m.sum (fun _ n => n) at he
  have hcoef : F.coeff (m + single i 1) ≠ 0 := by
    intro hzero
    have h := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv, hzero, zero_mul] at h
    exact h rfl
  have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoef)
  have hsum : (m + single i 1).sum (fun _ n => n) = m.sum (fun _ n => n) + 1 := by
    change (m + single i 1).degree = m.degree + 1
    rw [map_add, degree_single]
  rw [hsum, ← he] at hle
  omega

theorem nonconstant_of_irreducible (F : PlanePolynomial (K := K)) (hF : Irreducible F) :
    F ≠ C (F.coeff 0) := by
  intro hconstant
  have hcoef : F.coeff 0 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hconstant
    exact hF.ne_zero hconstant
  have hunit : IsUnit (C (F.coeff 0) : PlanePolynomial (K := K)) :=
    (isUnit_iff_ne_zero.mpr hcoef).map C
  exact hF.not_isUnit (hconstant.symm ▸ hunit)

variable [IsAlgClosed K]

theorem exists_zero_nonzero_of_not_dvd (F G : PlanePolynomial (K := K))
    (hF : Irreducible F) (hdiv : ¬ F ∣ G) :
    ∃ a : Fin 2 → K, eval a F = 0 ∧ eval a G ≠ 0 := by
  by_contra hn
  have hall : ∀ a : Fin 2 → K, eval a F = 0 → eval a G = 0 := by
    intro a ha
    by_contra hGa
    exact hn ⟨a, ha, hGa⟩
  let I : Ideal (PlanePolynomial (K := K)) := Ideal.span {F}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hF.prime
  have hG : G ∈ vanishingIdeal K (zeroLocus K I) := by
    rw [mem_vanishingIdeal_iff]
    intro a ha
    have hFa : eval a F = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using
        ha F (Ideal.mem_span_singleton_self F)
    simpa only [MvPolynomial.aeval_eq_eval] using hall a hFa
  rw [vanishingIdeal_zeroLocus_eq_radical, hI.radical] at hG
  exact hdiv (Ideal.mem_span_singleton.mp hG)

theorem exists_zero_with_nonzero_pderiv (F : PlanePolynomial (K := K))
    (hF : Irreducible F) (i : Fin 2) (hderiv : pderiv i F ≠ 0) :
    ∃ a : Fin 2 → K, eval a F = 0 ∧ eval a (pderiv i F) ≠ 0 := by
  apply exists_zero_nonzero_of_not_dvd F (pderiv i F) hF
  intro hdiv
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hderiv
  have hlt := pderiv_totalDegree_lt F i hderiv
  omega

theorem exists_smooth_point_of_degree_lt_char (p : ℕ) [CharP K p]
    (F : PlanePolynomial (K := K)) (hF : Irreducible F) (hdeg : F.totalDegree < p) :
    ∃ a : Fin 2 → K, eval a F = 0 ∧ ∃ i : Fin 2, eval a (pderiv i F) ≠ 0 := by
  obtain ⟨i, hi⟩ := FrobeniusLowDegree.exists_nonzero_pderiv_of_nonconstant p F hdeg
    (nonconstant_of_irreducible F hF)
  obtain ⟨a, ha, hai⟩ := exists_zero_with_nonzero_pderiv F hF i hi
  exact ⟨a, ha, i, hai⟩

end Cylinder.CurveSmoothPointExistence

end
