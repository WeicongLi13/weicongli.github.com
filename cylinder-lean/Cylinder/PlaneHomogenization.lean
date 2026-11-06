module

public import Cylinder.CurveSelfPolarExclusion
public import Cylinder.LinearEvaluationTransport
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Actual homogenization and an injective homogeneous affine chart

Homogenization is the finite sum of monomials with the missing degree
placed in the first coordinate. Evaluation in the chart recovers the
original polynomial. Injectivity on a fixed homogeneous degree is
proved by actual evaluation and rescaling on an infinite product set.
-/

@[expose] public section
noncomputable section

namespace Cylinder.PlaneHomogenization

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem dehomogenize_rename_some (F : PlanePolynomial (K := K)) :
    dehomogenize (rename (some : Fin 2 → Option (Fin 2)) F) = F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => simp [hF]

def homogenize (n : ℕ) (F : PlanePolynomial (K := K)) : HomogeneousPlanePolynomial (K := K) :=
  ∑ m ∈ F.support, X none ^ (n - m.degree) *
    rename (some : Fin 2 → Option (Fin 2)) (monomial m (F.coeff m))

theorem dehomogenize_homogenize (n : ℕ) (F : PlanePolynomial (K := K)) :
    dehomogenize (homogenize n F) = F := by
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_X_none,
    one_pow, one_mul, dehomogenize_rename_some]
  exact F.as_sum.symm

theorem homogenize_homogeneous (n : ℕ) (F : PlanePolynomial (K := K))
    (hdeg : F.totalDegree ≤ n) : (homogenize n F).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro m hm
  have hmdeg : m.degree ≤ n := (MvPolynomial.le_totalDegree hm).trans hdeg
  have hmono : (rename (some : Fin 2 → Option (Fin 2)) (monomial m (F.coeff m))).IsHomogeneous m.degree :=
    (isHomogeneous_monomial (F.coeff m) rfl).rename_isHomogeneous
  convert (isHomogeneous_X_pow (none : Option (Fin 2)) (n - m.degree)).mul hmono using 1
  omega

theorem dehomogenize_totalDegree_le (Q : HomogeneousPlanePolynomial (K := K)) :
    (dehomogenize Q).totalDegree ≤ Q.totalDegree := by
  let f : Option (Fin 2) → PlanePolynomial (K := K) := fun i => i.elim 1 X
  change (MvPolynomial.eval₂ C f Q).totalDegree ≤ Q.totalDegree
  rw [MvPolynomial.eval₂_eq']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  have hcoord : ∀ i, (f i).totalDegree ≤ 1 := by
    intro i
    cases i <;> simp [f]
  have hpows : ∀ i, (f i ^ m i).totalDegree ≤ m i := by
    intro i
    exact (totalDegree_pow _ _).trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left (m i) (hcoord i))
  have hprod : (∏ i, f i ^ m i).totalDegree ≤ ∑ i, m i :=
    (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => hpows i)
  have hsum : (∑ i, m i) ≤ Q.totalDegree := by
    have h := MvPolynomial.le_totalDegree hm
    change m.degree ≤ Q.totalDegree at h
    simpa only [Finsupp.degree_eq_sum] using h
  have hmul := totalDegree_mul (C (Q.coeff m)) (∏ i, f i ^ m i)
  rw [totalDegree_C, zero_add] at hmul
  exact hmul.trans (hprod.trans hsum)

variable [Infinite K]

theorem dehomogenize_zero_of_homogeneous (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hzero : dehomogenize Q = 0) : Q = 0 := by
  let sides : Option (Fin 2) → Set K := fun i => i.elim ({0}ᶜ) (fun _ => Set.univ)
  have hsides : ∀ i, (sides i).Infinite := by
    intro i
    cases i with
    | none => exact Set.Finite.infinite_compl (Set.finite_singleton 0)
    | some i => exact Set.infinite_univ
  apply MvPolynomial.funext_set sides hsides
  intro x hx
  rw [map_zero]
  have hxnone : x none ≠ 0 := by
    simpa only [sides, Option.elim_none, Set.mem_compl_iff, Set.mem_singleton_iff]
      using hx none (Set.mem_univ none)
  let u : K := (x none)⁻¹
  let z : Fin 2 → K := fun i => u * x (some i)
  have hnormalized : u • x = fun i => i.elim 1 z := by
    ext i
    cases i with
    | none => simp [u, hxnone, smul_eq_mul]
    | some i => simp [z, smul_eq_mul]
  have heval : eval (fun i => i.elim 1 z) Q = 0 := by
    rw [← eval_dehomogenize Q z, hzero, map_zero]
  have h := LinearEvaluationTransport.homogeneous_eval_smul Q n hQ u x
  rw [hnormalized, heval] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hxnone))

theorem dehomogenize_injective_on_homogeneous (n : ℕ)
    (Q R : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n) (hR : R.IsHomogeneous n)
    (heq : dehomogenize Q = dehomogenize R) : Q = R := by
  apply sub_eq_zero.mp
  apply dehomogenize_zero_of_homogeneous n (Q - R) (hQ.sub hR)
  rw [map_sub, heq, sub_self]

theorem homogenize_dehomogenize (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) : homogenize n (dehomogenize Q) = Q := by
  exact dehomogenize_injective_on_homogeneous n _ Q
    (homogenize_homogeneous n _ ((dehomogenize_totalDegree_le Q).trans hQ.totalDegree_le)) hQ
    (dehomogenize_homogenize n _)

omit [Infinite K] in
theorem first_coordinate_dvd_homogenize_of_degree_lt (n : ℕ) (F : PlanePolynomial (K := K))
    (hdeg : F.totalDegree < n) :
    (X none : HomogeneousPlanePolynomial (K := K)) ∣ homogenize n F := by
  unfold homogenize
  apply Finset.dvd_sum
  intro m hm
  have hmdeg : m.degree < n := lt_of_le_of_lt (MvPolynomial.le_totalDegree hm) hdeg
  apply dvd_mul_of_dvd_left
  have hpow : (X none : HomogeneousPlanePolynomial (K := K)) ^ 1 ∣ X none ^ (n - m.degree) :=
    pow_dvd_pow (X none) (by omega)
  simpa only [pow_one] using hpow

end Cylinder.PlaneHomogenization

end
