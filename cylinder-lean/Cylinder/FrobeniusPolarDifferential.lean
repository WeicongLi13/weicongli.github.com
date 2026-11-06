module

public import Cylinder.FrobeniusPolar
public import Mathlib.Tactic.LinearCombination

/-!
# Differential identities used in the self-polar argument

These are identities of actual polynomials and field derivations. The
construction of a curve function field, its smooth local parameters and
the intersection bound are separate tasks and are not asserted here.
-/

@[expose] public section

noncomputable section

namespace Cylinder.FrobeniusPolarDifferential

open MvPolynomial Cylinder.FrobeniusPolar
open scoped BigOperators Classical

variable {K σ : Type*} [Field K] [Fintype σ]

theorem polar_sub_euler (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) :
    polar p F - C (n : K) * F =
      ∑ i : σ, (X i ^ p - X i) * pderiv i F := by
  have heuler : ∑ i : σ, X i * pderiv i F = C (n : K) * F := by
    simpa only [nsmul_eq_mul, map_natCast] using hF.sum_X_mul_pderiv
  rw [← heuler, polar, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_polar_sub_euler (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (x : σ → K) :
    eval x (polar p F) - (n : K) * eval x F =
      ∑ i : σ, (x i ^ p - x i) * eval x (pderiv i F) := by
  have h := congrArg (eval x) (polar_sub_euler p n F hF)
  simpa only [map_sub, map_mul, map_sum, map_pow, eval_C, eval_X] using h

theorem self_polar_zero_relation (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (hdiv : F ∣ polar p F)
    (x : σ → K) (hzero : eval x F = 0) :
    (∑ i : σ, (x i ^ p - x i) * eval x (pderiv i F)) = 0 := by
  rw [← eval_polar_sub_euler p n F hF x, hzero, mul_zero, sub_zero]
  obtain ⟨G, hG⟩ := hdiv
  rw [hG, map_mul, hzero, zero_mul]

theorem affine_self_polar_relation (p n : ℕ) (F : MvPolynomial (Option σ) K)
    (hF : F.IsHomogeneous n) (hdiv : F ∣ polar p F) (x : σ → K)
    (hzero : eval (Option.elim · 1 x) F = 0) :
    (∑ i : σ, (x i ^ p - x i) *
      eval (Option.elim · 1 x) (pderiv (some i) F)) = 0 := by
  have h := self_polar_zero_relation p n F hF hdiv (Option.elim · 1 x) hzero
  simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some, one_pow,
    sub_self, zero_mul, zero_add] using h

section FieldDerivation

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]
variable (p : ℕ) [CharP L p] (D : Derivation R L L)

theorem derivation_frobenius_power (z : L) : D (z ^ p) = 0 := by
  rw [Derivation.leibniz_pow]
  simp [nsmul_eq_mul]

omit [CharP L p] in
theorem implicit_frobenius_relation (x y fx fy : L) (hfy : fy ≠ 0)
    (himplicit : D y = -fx / fy)
    (hpolar : (x ^ p - x) * fx + (y ^ p - y) * fy = 0) :
    (x ^ p - x) * D y = y ^ p - y := by
  have hnum : -((x ^ p - x) * fx) = (y ^ p - y) * fy := by
    linear_combination -hpolar
  rw [himplicit]
  calc
    _ = -((x ^ p - x) * fx) / fy := by ring
    _ = _ := (div_eq_iff hfy).mpr hnum

theorem second_derivative_eq_zero (x y : L) (hx : D x = 1)
    (hxnonzero : x ^ p - x ≠ 0)
    (hrelation : (x ^ p - x) * D y = y ^ p - y) : D (D y) = 0 := by
  have h := congrArg D hrelation
  simp only [Derivation.leibniz, map_sub, derivation_frobenius_power,
    hx, smul_eq_mul, zero_sub] at h
  have hmul : (x ^ p - x) * D (D y) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left hxnonzero

theorem self_polar_implicit_second_derivative (x y fx fy : L)
    (hx : D x = 1) (hxnonzero : x ^ p - x ≠ 0) (hfy : fy ≠ 0)
    (himplicit : D y = -fx / fy)
    (hpolar : (x ^ p - x) * fx + (y ^ p - y) * fy = 0) : D (D y) = 0 :=
  second_derivative_eq_zero p D x y hx hxnonzero
    (implicit_frobenius_relation p D x y fx fy hfy himplicit hpolar)

end FieldDerivation

end Cylinder.FrobeniusPolarDifferential

end
