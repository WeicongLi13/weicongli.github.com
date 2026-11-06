module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial identities for the Frobenius polar

The polar is the actual sum of Frobenius powers times partial derivatives.
Rational representatives are characterized by Frobenius-fixed coordinates.
This file proves its degree, vanishing and tangent identities. It does not
assert an intersection-multiplicity estimate or a plane-curve Bezout bound.
-/

@[expose] public section

noncomputable section

namespace Cylinder.FrobeniusPolar

open MvPolynomial
open scoped BigOperators Classical

variable {K σ : Type*} [Field K] [Fintype σ]

def polar (p : ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i : σ, X i ^ p * pderiv i F

def theta (p : ℕ) : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  mkDerivation K (fun i : σ => X i ^ p)

theorem theta_eq_sum (p : ℕ) :
    theta (K := K) (σ := σ) p =
      ∑ i : σ, (X i ^ p : MvPolynomial σ K) • pderiv (R := K) i := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [theta, Pi.single_apply, smul_eq_mul]

theorem theta_apply (p : ℕ) (F : MvPolynomial σ K) : theta p F = polar p F := by
  rw [theta_eq_sum]
  simp [polar, smul_eq_mul]

theorem polar_homogeneous (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) : (polar p F).IsHomogeneous (p + (n - 1)) := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X_pow i p).mul hF.pderiv

theorem polar_homogeneous_of_pos (p n : ℕ) (hn : 0 < n) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) : (polar p F).IsHomogeneous (n + p - 1) := by
  convert polar_homogeneous p n F hF using 1
  omega

theorem polar_totalDegree_le (p n : ℕ) (hn : 0 < n) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) : (polar p F).totalDegree ≤ n + p - 1 :=
  (polar_homogeneous_of_pos p n hn F hF).totalDegree_le

theorem polar_totalDegree (p n : ℕ) (hn : 0 < n) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (hpolar : polar p F ≠ 0) :
    (polar p F).totalDegree = n + p - 1 :=
  (polar_homogeneous_of_pos p n hn F hF).totalDegree hpolar

def FrobeniusFixed (p : ℕ) (x : σ → K) : Prop := ∀ i, x i ^ p = x i

omit [Fintype σ] in
theorem frobeniusFixed_primeField (p : ℕ) [Fact p.Prime] (x : σ → ZMod p) :
    FrobeniusFixed p x := fun i => ZMod.pow_card (x i)

omit [Fintype σ] in
theorem frobeniusFixed_primeField_image (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (x : σ → ZMod p) : FrobeniusFixed p (fun i => f (x i)) := by
  intro i
  rw [← map_pow, ZMod.pow_card]

theorem eval_polar_at_fixed (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (x : σ → K) (hx : FrobeniusFixed p x) :
    eval x (polar p F) = (n : K) * eval x F := by
  calc
    _ = eval x (∑ i : σ, X i * pderiv i F) := by
      simp only [polar, map_sum, map_mul, map_pow, eval_X]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i]
    _ = _ := by rw [hF.sum_X_mul_pderiv]; simp [nsmul_eq_mul]

theorem polar_vanishes_at_rational_zero (p n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (x : σ → K) (hx : FrobeniusFixed p x)
    (hzero : eval x F = 0) : eval x (polar p F) = 0 := by
  rw [eval_polar_at_fixed p n F hF x hx, hzero, mul_zero]

variable (p : ℕ) [CharP K p]

omit [Fintype σ] in
theorem pderiv_frobenius_power (i j : σ) :
    pderiv j (X i ^ p : MvPolynomial σ K) = 0 := by
  rw [pderiv_pow]
  simp

theorem pderiv_polar (F : MvPolynomial σ K) (j : σ) :
    pderiv j (polar p F) = polar p (pderiv j F) := by
  simp only [polar, map_sum, pderiv_mul, pderiv_frobenius_power,
    zero_mul, zero_add, pderiv_comm j]

def gradient (F : MvPolynomial σ K) (x : σ → K) : σ → K :=
  fun j => eval x (pderiv j F)

theorem gradient_polar_at_fixed (n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (x : σ → K) (hx : FrobeniusFixed p x) :
    gradient (polar p F) x = (n - 1 : ℕ) • gradient F x := by
  funext j
  rw [gradient, pderiv_polar]
  change eval x (polar p (pderiv j F)) = (n - 1) • eval x (pderiv j F)
  simpa only [nsmul_eq_mul] using
    eval_polar_at_fixed p (n - 1) (pderiv j F) hF.pderiv x hx

def tangentForm (F : MvPolynomial σ K) (x : σ → K) : MvPolynomial σ K :=
  ∑ j : σ, C (gradient F x j) * X j

theorem tangentForm_homogeneous (F : MvPolynomial σ K) (x : σ → K) :
    (tangentForm F x).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

@[simp] theorem eval_tangentForm_single (F : MvPolynomial σ K) (x : σ → K) (j : σ) :
    eval (Pi.single j 1) (tangentForm F x) = gradient F x j := by
  simp [tangentForm, Pi.single_apply]

theorem tangentForm_eq_zero_iff (F : MvPolynomial σ K) (x : σ → K) :
    tangentForm F x = 0 ↔ gradient F x = 0 := by
  constructor
  · intro h
    funext j
    have he := eval_tangentForm_single F x j
    rw [h, map_zero] at he
    exact he.symm
  · intro h
    simp [tangentForm, h]

theorem tangentForm_polar_at_fixed (n : ℕ) (F : MvPolynomial σ K)
    (hF : F.IsHomogeneous n) (x : σ → K) (hx : FrobeniusFixed p x) :
    tangentForm (polar p F) x = C ((n - 1 : ℕ) : K) * tangentForm F x := by
  rw [tangentForm, gradient_polar_at_fixed p n F hF x hx]
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, tangentForm, Finset.mul_sum, mul_assoc]

theorem degree_minus_one_ne_zero (n : ℕ) (hn : 2 ≤ n) (hnp : n < p) :
    ((n - 1 : ℕ) : K) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff K p (n - 1)).mp h
  have hz : n - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem gradient_polar_eq_zero_iff (n : ℕ) (hn : 2 ≤ n) (hnp : n < p)
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous n)
    (x : σ → K) (hx : FrobeniusFixed p x) :
    gradient (polar p F) x = 0 ↔ gradient F x = 0 := by
  rw [gradient_polar_at_fixed p n F hF x hx]
  constructor
  · intro h
    funext j
    have he := congrFun h j
    change (n - 1) • gradient F x j = 0 at he
    rw [nsmul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (degree_minus_one_ne_zero (K := K) p n hn hnp)
  · intro h
    rw [h, smul_zero]

theorem tangent_polar_zeros_iff (n : ℕ) (hn : 2 ≤ n) (hnp : n < p)
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous n)
    (x y : σ → K) (hx : FrobeniusFixed p x) :
    eval y (tangentForm (polar p F) x) = 0 ↔ eval y (tangentForm F x) = 0 := by
  rw [tangentForm_polar_at_fixed p n F hF x hx, map_mul, eval_C]
  exact mul_eq_zero_iff_left (degree_minus_one_ne_zero (K := K) p n hn hnp)

omit [CharP K p] in
theorem polar_power (F : MvPolynomial σ K) (m : ℕ) :
    polar p (F ^ m) = (m : K) • (F ^ (m - 1) * polar p F) := by
  rw [← theta_apply, Derivation.leibniz_pow, theta_apply]
  simp [nsmul_eq_mul, smul_eq_mul, smul_eq_C_mul]

omit [CharP K p] in
theorem power_pred_dvd_polar_power (F : MvPolynomial σ K) (m : ℕ) :
    F ^ (m - 1) ∣ polar p (F ^ m) := by
  rw [polar_power]
  use C (m : K) * polar p F
  simp only [smul_eq_C_mul]
  ring

theorem polar_power_of_char_dvd (F : MvPolynomial σ K) (m : ℕ) (hm : p ∣ m) :
    polar p (F ^ m) = 0 := by
  rw [polar_power, (CharP.cast_eq_zero_iff K p m).mpr hm, zero_smul]

end Cylinder.FrobeniusPolar

end
