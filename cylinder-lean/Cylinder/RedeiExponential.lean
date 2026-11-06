module

public import Cylinder.Geometry
public import Cylinder.PowerSums
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! The truncated exponential and the factorization identity in characteristic p.
All polynomial congruences below are formal polynomial identities. -/
@[expose] public section
noncomputable section
namespace Cylinder.Redei
open scoped BigOperators Classical Polynomial
open Finset Polynomial

variable (p : ℕ) [Fact p.Prime]
variable {R : Type*} [CommRing R] [Algebra (ZMod p) R]

/-- Coefficients of the exponential in degrees strictly below the characteristic. -/
def invFac (R : Type*) [CommRing R] [Algebra (ZMod p) R] (j : ℕ) : R :=
  algebraMap (ZMod p) R ((j.factorial : ZMod p)⁻¹)

def expPoly (a : R) : R[X] :=
  ∑ k ∈ range p, monomial k (invFac p R k * a ^ k)

theorem expPoly_coeff (a : R) (j : ℕ) :
    (expPoly p a).coeff j = if j < p then invFac p R j * a ^ j else 0 := by
  classical
  simp [expPoly, finsetSum_coeff, coeff_monomial]

private theorem fac_ne_zero {j : ℕ} (hj : j < p) : (j.factorial : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial]
  omega

private theorem invFac_binomial {n k : ℕ} (hn : n < p) (hk : k ≤ n) :
    invFac p R k * invFac p R (n-k) = invFac p R n * (n.choose k : R) := by
  have ha := fac_ne_zero p (lt_of_le_of_lt hk hn)
  have hb := fac_ne_zero p (show n-k < p by omega)
  have hc := fac_ne_zero p hn
  have h : (n.choose k : ZMod p) * (k.factorial : ZMod p) *
      ((n-k).factorial : ZMod p) = (n.factorial : ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun m : ℕ => (m : ZMod p))
      (Nat.choose_mul_factorial_mul_factorial hk)
  have hz : ((k.factorial : ZMod p)⁻¹) * (((n-k).factorial : ZMod p)⁻¹) =
      ((n.factorial : ZMod p)⁻¹) * (n.choose k : ZMod p) := by
    field_simp
    linear_combination -h
  simpa only [invFac, map_mul, map_natCast] using congrArg (algebraMap (ZMod p) R) hz

/-- In degree below p, multiplication of the two exponential series
is the binomial theorem, with invertible factorials. -/
theorem expPoly_add_dvd (a b : R) :
    (X : R[X]) ^ p ∣ expPoly p a * expPoly p b - expPoly p (a+b) := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [coeff_sub, sub_eq_zero, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (expPoly p a).coeff i * (expPoly p b).coeff j) n,
    expPoly_coeff, ite_eq_left hn, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  rw [expPoly_coeff, expPoly_coeff, ite_eq_left (lt_of_le_of_lt hkn hn),
    ite_eq_left (show n-k < p by omega)]
  linear_combination (a^k * b^(n-k)) * invFac_binomial (R := R) p hn hkn

private theorem expPoly_comp_scale (a z : R) :
    (expPoly p a).comp (C z * X) = expPoly p (a*z) := by
  simp only [expPoly, Polynomial.sum_comp, monomial_comp]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  ring

/-- If z^p=0 the congruence becomes equality after the substitution X ↦ zX. -/
theorem expPoly_mul_nilpotent (a b z : R) (hz : z ^ p = 0) :
    expPoly p (a*z) * expPoly p (b*z) = expPoly p ((a+b)*z) := by
  obtain ⟨P,hP⟩ := expPoly_add_dvd p a b
  have h := congrArg (Polynomial.compRingHom (C z * X)) hP
  rw [map_sub, map_mul, map_mul, map_pow] at h
  change (expPoly p a).comp (C z * X) * (expPoly p b).comp (C z * X) -
    (expPoly p (a+b)).comp (C z * X) = X.comp (C z * X) ^ p * P.comp (C z * X) at h
  simpa only [expPoly_comp_scale, X_comp, mul_pow, ← map_pow, hz, map_zero, zero_mul,
    sub_eq_zero] using h

/-- Reducing modulo the p-th power of the auxiliary variable combines all
coordinate exponentials into the exponential of the dot product. -/
theorem expPoly_prod_dvd {ι : Type*} (s : Finset ι) (a : ι → R) :
    (X : R[X])^p ∣ (∏ i ∈ s, expPoly p (a i)) - expPoly p (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    suffices hz : expPoly p (0 : R) = 1 by simp [hz]
    ext k
    by_cases h : k = 0
    · subst k; simp [expPoly_coeff, invFac, (Fact.out : p.Prime).pos]
    · simp [expPoly_coeff, zero_pow h, coeff_one, h]
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    obtain ⟨P,hP⟩ := ih
    obtain ⟨Q,hQ⟩ := expPoly_add_dvd p (a i) (∑ j ∈ s, a j)
    exact ⟨expPoly p (a i) * P + Q, by linear_combination expPoly p (a i) * hP + hQ⟩

/-- The polynomial attached to a vector, in a separate variable recording degree. -/
def expWeight (z : Fin 3 → R) (x : Geometry.Point p) : R[X] :=
  ∏ i, expPoly p (algebraMap (ZMod p) R (x i) * z i)

theorem expWeight_coeff (z : Fin 3 → R) (x : Geometry.Point p) (j : ℕ) (hj : j < p) :
    (expWeight p z x).coeff j =
      invFac p R j * (∑ i, algebraMap (ZMod p) R (x i) * z i)^j := by
  have h := (X_pow_dvd_iff.mp (expPoly_prod_dvd p Finset.univ
    (fun i => algebraMap (ZMod p) R (x i) * z i))) j hj
  simpa only [coeff_sub, expPoly_coeff, ite_eq_left hj, sub_eq_zero, expWeight] using h

theorem expWeight_mul (z : Fin 3 → R) (hz : ∀ i, z i ^ p = 0) (a b : Geometry.Point p) :
    expWeight p z a * expWeight p z b = expWeight p z (a+b) := by
  rw [expWeight, expWeight, expWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Pi.add_apply, map_add] using
    expPoly_mul_nilpotent p (algebraMap (ZMod p) R (a i)) (algebraMap (ZMod p) R (b i))
      (z i) (hz i)

private theorem sum_scalar_exp (z : R) :
    ∃ c : R, (∑ t : ZMod p, expPoly p (algebraMap (ZMod p) R t * z)) =
      monomial (p-1) c := by
  classical
  refine ⟨(∑ t : ZMod p, expPoly p (algebraMap (ZMod p) R t * z)).coeff (p-1), ?_⟩
  ext k
  by_cases he : k = p-1
  · subst k; simp
  rw [coeff_monomial, ite_eq_right (Ne.symm he)]
  rw [finsetSum_coeff]
  by_cases hk : k < p
  · simp only [expPoly_coeff, ite_eq_left hk, mul_pow, ← map_pow]
    have hl : k < p-1 := by omega
    calc
      _ = invFac p R k * algebraMap (ZMod p) R (∑ t : ZMod p, t^k) * z^k := by
        simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro _ _
        ring
      _ = 0 := by rw [PowerSums.prime_sum_pow_low p k hl, map_zero, mul_zero, zero_mul]
  · simp [expPoly_coeff, hk]

/-- Unique representation turns the product into a single monomial of degree
3(p−1) when each coordinate is p-nilpotent. -/
theorem tiling_exp_product (z : Fin 3 → R) (hz : ∀ i, z i ^ p = 0)
    (A B : Finset (Geometry.Point p))
    (hab : AddSubgroup.IsComplement (A : Set (Geometry.Point p)) B) :
    ∃ c : R, (∑ x ∈ A, expWeight p z x) * (∑ x ∈ B, expWeight p z x) =
      monomial (3*(p-1)) c := by
  classical
  choose c hc using fun i : Fin 3 => sum_scalar_exp p (z i)
  refine ⟨∏ i, c i, ?_⟩
  let e : (A × B) ≃ Geometry.Point p := Equiv.ofBijective _ hab
  calc
    _ = ∑ ab : A × B, expWeight p z (e ab) := by
      change _ = ∑ ab : A × B, expWeight p z ((ab.1 : Geometry.Point p) + ab.2)
      rw [← Finset.sum_coe_sort A (expWeight p z), ← Finset.sum_coe_sort B (expWeight p z)]
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp_rw [Finset.mul_sum, ← expWeight_mul p z hz]
    _ = ∑ x : Geometry.Point p, expWeight p z x := e.sum_comp _
    _ = ∏ i, ∑ t : ZMod p, expPoly p (algebraMap (ZMod p) R t * z i) :=
      (Fintype.prod_sum (ι := Fin 3) (κ := fun _ => ZMod p)
        (fun i t => expPoly p (algebraMap (ZMod p) R t * z i))).symm
    _ = _ := by
      simp_rw [hc]
      have hn : 3*(p-1) = (p-1) + ((p-1)+(p-1)) := by omega
      simp only [Fin.prod_univ_three, monomial_mul_monomial, hn, add_assoc, mul_assoc]

end Cylinder.Redei
end
