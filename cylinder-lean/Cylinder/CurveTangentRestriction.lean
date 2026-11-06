module

public import Cylinder.CurveSelfPolarParameter
public import Cylinder.AffineLinePolynomial
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# High formal contact forces an actual tangent-line factor

Restriction to the tangent is a genuine one-variable polynomial of
degree at most the original total degree. The difference of two
evaluations is divisible by the difference of their second coordinates.
Thus contact of order `p`, for degree below `p`, makes the restriction
zero and produces an actual linear divisor. The self-polar exclusion
here is for an irreducible polynomial with a smooth point at the origin;
existence of a smooth point on a general curve is a separate theorem.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CurveTangentRestriction

open MvPolynomial Cylinder.CurveLocalParameter
open scoped Classical

variable {K : Type*} [Field K]

@[simp] theorem along_X_zero (x y : PowerSeries K) : along x y (X 0) = x := by
  simp [along]

@[simp] theorem along_X_one (x y : PowerSeries K) : along x y (X 1) = y := by
  simp [along]

theorem second_coordinate_sub_dvd (F : PlanePolynomial (K := K))
    (x y z : PowerSeries K) : y - z ∣ along x y F - along x z F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [along]
  | add F G hF hG =>
    simp only [map_add]
    rw [show along x y F + along x y G - (along x z F + along x z G) =
      (along x y F - along x z F) + (along x y G - along x z G) by ring]
    exact dvd_add hF hG
  | mul_X F i hF =>
    simp only [map_mul]
    fin_cases i
    · simpa [along, sub_mul] using dvd_mul_of_dvd_left hF x
    · have hd : y - z ∣ (y - z) * along x y F +
          (along x y F - along x z F) * z :=
        dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hF z)
      convert hd using 1
      simp [along]
      ring

def tangentRestriction (t : K) : PlanePolynomial (K := K) →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C t * Polynomial.X]

theorem tangentRestriction_eq_linePolynomial (F : PlanePolynomial (K := K)) (t : K) :
    tangentRestriction t F = AffineLinePolynomial.linePolynomial F 0 ![1, t] := by
  change MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, Polynomial.C t * Polynomial.X] F = _
  unfold AffineLinePolynomial.linePolynomial
  congr 1
  funext i
  fin_cases i <;> simp [AffineLinePolynomial.affineLinear]

theorem tangentRestriction_degree_le (F : PlanePolynomial (K := K)) (t : K) :
    (tangentRestriction t F).natDegree ≤ F.totalDegree := by
  rw [tangentRestriction_eq_linePolynomial]
  exact AffineLinePolynomial.linePolynomial_degree_le F 0 ![1, t]

theorem coe_tangentRestriction (F : PlanePolynomial (K := K)) (t : K) :
    ((tangentRestriction t F : Polynomial K) : PowerSeries K) =
      along PowerSeries.X (PowerSeries.C t * PowerSeries.X) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [tangentRestriction, along]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, Polynomial.coe_mul, hF]
    congr 1
    fin_cases i <;> simp [tangentRestriction, along]

theorem polynomial_eq_zero_of_X_pow_dvd_coe (P : Polynomial K) (p : ℕ)
    (hdeg : P.natDegree < p)
    (hdiv : (PowerSeries.X : PowerSeries K) ^ p ∣ (P : PowerSeries K)) : P = 0 := by
  ext j
  by_cases hj : j < p
  · have h := PowerSeries.X_pow_dvd_iff.mp hdiv j hj
    simpa only [Polynomial.coeff_coe, Polynomial.coeff_zero] using h
  · rw [Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (by omega))

theorem tangentRestriction_eq_zero_of_high_contact (F : PlanePolynomial (K := K)) (p : ℕ)
    (hdeg : F.totalDegree < p) (y : PowerSeries K) (t : K)
    (hyF : along PowerSeries.X y F = 0)
    (hcontact : (PowerSeries.X : PowerSeries K) ^ p ∣ y - PowerSeries.C t * PowerSeries.X) :
    tangentRestriction t F = 0 := by
  apply polynomial_eq_zero_of_X_pow_dvd_coe _ p
    (lt_of_le_of_lt (tangentRestriction_degree_le F t) hdeg)
  rw [coe_tangentRestriction]
  have h := hcontact.trans
    (second_coordinate_sub_dvd F PowerSeries.X y (PowerSeries.C t * PowerSeries.X))
  rw [hyF, zero_sub] at h
  exact dvd_neg.mp h

def tangentLine (t : K) : PlanePolynomial (K := K) := X 1 - C t * X 0

theorem eval_bivariate_tangent (F : PlanePolynomial (K := K)) (t : K) :
    ((Polynomial.Bivariate.equivMvPolynomial K).symm F).eval
      (Polynomial.C t * Polynomial.X) = tangentRestriction t F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [tangentRestriction]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, Polynomial.eval_mul, hF]
    congr 1
    fin_cases i <;> simp [tangentRestriction]

theorem tangentLine_dvd_of_restriction_zero (F : PlanePolynomial (K := K)) (t : K)
    (hzero : tangentRestriction t F = 0) : tangentLine t ∣ F := by
  have hdiv : Polynomial.X - Polynomial.C (Polynomial.C t * Polynomial.X) ∣
      (Polynomial.Bivariate.equivMvPolynomial K).symm F := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_bivariate_tangent, hzero]
  simpa [tangentLine] using map_dvd
    (Polynomial.Bivariate.equivMvPolynomial K).toRingHom hdiv

theorem tangentLine_homogeneous (t : K) : (tangentLine t).IsHomogeneous 1 :=
  (isHomogeneous_X K 1).sub (isHomogeneous_C_mul_X t 0)

theorem tangentLine_ne_zero (t : K) : tangentLine t ≠ 0 := by
  intro hzero
  have h := congrArg (eval ![0, 1]) hzero
  simp [tangentLine] at h

theorem tangentLine_totalDegree (t : K) : (tangentLine t).totalDegree = 1 :=
  (tangentLine_homogeneous t).totalDegree (tangentLine_ne_zero t)

theorem tangentLine_not_isUnit (t : K) : ¬ IsUnit (tangentLine t) := by
  intro hunit
  have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rw [tangentLine_totalDegree] at hdeg
  exact Nat.one_ne_zero hdeg

theorem degree_le_one_of_irreducible_tangentLine_dvd (F : PlanePolynomial (K := K))
    (hF : Irreducible F) (t : K) (hdiv : tangentLine t ∣ F) : F.totalDegree ≤ 1 := by
  have ha := (hF.dvd_iff.mp hdiv).resolve_left (tangentLine_not_isUnit t)
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain ha.dvd (tangentLine_ne_zero t)
  simpa only [tangentLine_totalDegree] using hd

theorem not_self_polar_at_smooth_origin (p n : ℕ) [CharP K p]
    (F : PlanePolynomial (K := K)) (hF : Irreducible F)
    (hdeg : F.totalDegree < p) (hnonlinear : 2 ≤ F.totalDegree)
    (hzero : eval (0 : Fin 2 → K) F = 0)
    (hY : eval (0 : Fin 2 → K) (pderiv 1 F) ≠ 0) :
    ¬ F ∣ CurveSelfPolarParameter.affinePolar p n F := by
  intro hdiv
  obtain ⟨y, hy0, hyF, horder⟩ := CurveSelfPolarParameter.exists_self_polar_parameter p n F hzero hY hdiv
  have hcontact : (PowerSeries.X : PowerSeries K) ^ p ∣
      y - PowerSeries.C (PowerSeries.coeff 1 y) * PowerSeries.X := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    have h := PowerSeries.nat_le_order_iff.mp horder
    simpa only [FrobeniusPolarSeries.linearTruncation, hy0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_zero, zero_add] using h
  have hrestriction := tangentRestriction_eq_zero_of_high_contact F p hdeg y
    (PowerSeries.coeff 1 y) hyF hcontact
  have hline := tangentLine_dvd_of_restriction_zero F _ hrestriction
  have hdegree := degree_le_one_of_irreducible_tangentLine_dvd F hF _ hline
  omega

end Cylinder.CurveTangentRestriction

end
