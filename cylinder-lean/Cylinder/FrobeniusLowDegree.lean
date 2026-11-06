module

public import Cylinder.FrobeniusPolar

/-!
# Partial derivatives below the characteristic

A polynomial of total degree below the characteristic whose partial
derivatives all vanish is constant. The proof uses its actual monomial
coefficients, rather than a separability assumption.
-/

@[expose] public section

noncomputable section

namespace Cylinder.FrobeniusLowDegree

open MvPolynomial Finsupp
open scoped BigOperators Classical

variable {K σ : Type*} [Field K]
variable (p : ℕ) [CharP K p]

theorem constant_of_pderiv_eq_zero (F : MvPolynomial σ K) (hdeg : F.totalDegree < p)
    (hderiv : ∀ i, pderiv i F = 0) : F = C (F.coeff 0) := by
  ext m
  rw [coeff_C]
  split_ifs with hm
  · subst m
    rfl
  · by_cases hcoef : F.coeff m = 0
    · exact hcoef
    · have hmem : m ∈ F.support := MvPolynomial.mem_support_iff.mpr hcoef
      have hi : ∃ i, m i ≠ 0 := by
        by_contra hi
        push Not at hi
        have hmzero : m = 0 := Finsupp.ext hi
        exact hm hmzero.symm
      obtain ⟨i, hmi⟩ := hi
      have hmip : m i < p :=
        lt_of_le_of_lt ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr hmi)).trans (le_totalDegree hmem)) hdeg
      have hcast : (m i : K) ≠ 0 := by
        intro hz
        have hd := (CharP.cast_eq_zero_iff K p (m i)).mp hz
        exact hmi (Nat.eq_zero_of_dvd_of_lt hd hmip)
      have hcoeff := congrArg (fun G : MvPolynomial σ K => G.coeff (m - single i 1))
        (hderiv i)
      rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hmi] at hcoeff
      have he : (m - single i 1 : σ →₀ ℕ) i + 1 = m i := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      have hecast : (((m - single i 1 : σ →₀ ℕ) i : ℕ) : K) + 1 = (m i : K) := by
        simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) he
      rw [hecast] at hcoeff
      exact False.elim (hcoef ((mul_eq_zero.mp hcoeff).resolve_right hcast))

theorem exists_nonzero_pderiv_of_nonconstant (F : MvPolynomial σ K)
    (hdeg : F.totalDegree < p) (hnonconstant : F ≠ C (F.coeff 0)) :
    ∃ i, pderiv i F ≠ 0 := by
  by_contra h
  push Not at h
  exact hnonconstant (constant_of_pderiv_eq_zero p F hdeg h)

end Cylinder.FrobeniusLowDegree

end
