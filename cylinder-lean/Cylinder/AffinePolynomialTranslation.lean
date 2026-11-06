module

public import Cylinder.CurveTangentRestriction
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! Actual translations of plane equations, including degree and irreducibility. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffinePolynomialTranslation

open MvPolynomial Cylinder.CurveLocalParameter
open scoped BigOperators Classical

variable {K : Type*} [Field K]

def translate (a : Fin 2 → K) : PlanePolynomial (K := K) →+* PlanePolynomial (K := K) :=
  eval₂Hom C (fun i => C (a i) + X i)

@[simp] theorem translate_C (a : Fin 2 → K) (c : K) : translate a (C c) = C c := by
  simp [translate]

@[simp] theorem translate_X (a : Fin 2 → K) (i : Fin 2) :
    translate a (X i) = C (a i) + X i := by simp [translate]

theorem translate_translate (a b : Fin 2 → K) (F : PlanePolynomial (K := K)) :
    translate a (translate b F) = translate (a + b) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF, translate_X, map_add, translate_C, Pi.add_apply]
    ring

@[simp] theorem translate_zero (F : PlanePolynomial (K := K)) : translate 0 F = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => simp [hF]

def translationEquiv (a : Fin 2 → K) : PlanePolynomial (K := K) ≃+* PlanePolynomial (K := K) where
  toFun := translate a
  invFun := translate (-a)
  left_inv F := by rw [translate_translate]; simp
  right_inv F := by rw [translate_translate]; simp
  map_mul' F G := map_mul (translate a) F G
  map_add' F G := map_add (translate a) F G

theorem translate_irreducible (a : Fin 2 → K) (F : PlanePolynomial (K := K)) :
    Irreducible (translate a F) ↔ Irreducible F :=
  MulEquiv.irreducible_iff (f := (translationEquiv a).toMulEquiv)

theorem translated_coordinate_degree_le (a : Fin 2 → K) (i : Fin 2) :
    (C (a i) + X i : PlanePolynomial (K := K)).totalDegree ≤ 1 := by
  exact (totalDegree_add _ _).trans (by simp)

theorem translated_coordinate_pow_degree_le (a : Fin 2 → K) (i : Fin 2) (n : ℕ) :
    ((C (a i) + X i : PlanePolynomial (K := K)) ^ n).totalDegree ≤ n :=
  (totalDegree_pow _ n).trans (by
    simpa only [mul_one] using Nat.mul_le_mul_left n (translated_coordinate_degree_le a i))

theorem translate_totalDegree_le (a : Fin 2 → K) (F : PlanePolynomial (K := K)) :
    (translate a F).totalDegree ≤ F.totalDegree := by
  change (MvPolynomial.eval₂ C (fun i => C (a i) + X i) F).totalDegree ≤ F.totalDegree
  rw [MvPolynomial.eval₂_eq']
  simp only [Fin.prod_univ_two]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  let A : PlanePolynomial (K := K) := C (a 0) + X 0
  let B : PlanePolynomial (K := K) := C (a 1) + X 1
  change (C (F.coeff m) * (A ^ m 0 * B ^ m 1)).totalDegree ≤ F.totalDegree
  have h1 := totalDegree_mul (C (F.coeff m)) (A ^ m 0 * B ^ m 1)
  have h2 := totalDegree_mul (A ^ m 0) (B ^ m 1)
  have h3 := translated_coordinate_pow_degree_le a 0 (m 0)
  have h4 := translated_coordinate_pow_degree_le a 1 (m 1)
  have h5 := MvPolynomial.le_totalDegree hm
  change m.degree ≤ F.totalDegree at h5
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h5
  calc
    _ ≤ (C (F.coeff m)).totalDegree + (A ^ m 0 * B ^ m 1).totalDegree := h1
    _ = (A ^ m 0 * B ^ m 1).totalDegree := by rw [totalDegree_C, zero_add]
    _ ≤ (A ^ m 0).totalDegree + (B ^ m 1).totalDegree := h2
    _ ≤ m 0 + m 1 := add_le_add h3 h4
    _ ≤ F.totalDegree := h5

theorem translate_totalDegree (a : Fin 2 → K) (F : PlanePolynomial (K := K)) :
    (translate a F).totalDegree = F.totalDegree := by
  apply le_antisymm (translate_totalDegree_le a F)
  have h := translate_totalDegree_le (-a) (translate a F)
  rw [translate_translate] at h
  simpa only [neg_add_cancel, translate_zero] using h

theorem pderiv_translate (a : Fin 2 → K) (F : PlanePolynomial (K := K)) (j : Fin 2) :
    pderiv j (translate a F) = translate a (pderiv j F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, translate_X, pderiv_mul, map_add, hF, map_mul]
    by_cases hi : i = j
    · subst i
      simp
    · simp [pderiv_X_of_ne hi]

theorem eval_translate (a x : Fin 2 → K) (F : PlanePolynomial (K := K)) :
    eval x (translate a F) = eval (a + x) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF => simp [hF, Pi.add_apply]

theorem along_translate (a : Fin 2 → K) (F : PlanePolynomial (K := K))
    (x y : PowerSeries K) : along x y (translate a F) =
    along (PowerSeries.C (a 0) + x) (PowerSeries.C (a 1) + y) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [along]
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF, translate_X, map_add]
    congr 1
    fin_cases i <;> simp [along]

end Cylinder.AffinePolynomialTranslation

end
