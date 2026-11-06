module

public import Cylinder.CurveParameterAtPoint

/-!
# Self-polar exclusion for an arbitrary irreducible affine plane curve

The smooth point is obtained from the Nullstellensatz. A coordinate
exchange chooses a nonzero second partial derivative, and the actual
translated parameter gives a tangent-line divisor by the degree bound.
No smooth-point or contact assumption is included in the final theorem.
The homogeneous/projective dehomogenization bridge is separate.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CurveSelfPolarExclusion

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.AffinePolynomialTranslation
open Cylinder.CurveTangentRestriction Cylinder.CurveParameterAtPoint
open scoped Classical

variable {K : Type*} [Field K]

theorem not_self_polar_at_smooth_point (p n : ℕ) [CharP K p]
    (F : PlanePolynomial (K := K)) (hF : Irreducible F)
    (hdeg : F.totalDegree < p) (hnonlinear : 2 ≤ F.totalDegree)
    (a : Fin 2 → K) (hzero : eval a F = 0) (hY : eval a (pderiv 1 F) ≠ 0) :
    ¬ F ∣ CurveSelfPolarParameter.affinePolar p n F := by
  intro hdiv
  obtain ⟨y, hy0, hyF, horder⟩ := exists_self_polar_parameter_at_point p n F a hzero hY hdiv
  have hytranslate : along PowerSeries.X y (translate a F) = 0 := by
    rwa [along_translate]
  have hcontact : (PowerSeries.X : PowerSeries K) ^ p ∣
      y - PowerSeries.C (PowerSeries.coeff 1 y) * PowerSeries.X := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    have h := PowerSeries.nat_le_order_iff.mp horder
    simpa only [FrobeniusPolarSeries.linearTruncation, hy0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_zero, zero_add] using h
  have hrestriction := tangentRestriction_eq_zero_of_high_contact (translate a F) p
    (by rwa [translate_totalDegree]) y (PowerSeries.coeff 1 y) hytranslate hcontact
  have hline := tangentLine_dvd_of_restriction_zero (translate a F) _ hrestriction
  have hdegree := degree_le_one_of_irreducible_tangentLine_dvd (translate a F)
    ((translate_irreducible a F).mpr hF) _ hline
  rw [translate_totalDegree] at hdegree
  omega

def flip : PlanePolynomial (K := K) ≃ₐ[K] PlanePolynomial (K := K) :=
  MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)

@[simp] theorem flip_C (c : K) : flip (C c) = C c := by simp [flip]

@[simp] theorem flip_X_zero : flip (X 0 : PlanePolynomial (K := K)) = X 1 := by simp [flip]

@[simp] theorem flip_X_one : flip (X 1 : PlanePolynomial (K := K)) = X 0 := by simp [flip]

theorem pderiv_zero_flip (F : PlanePolynomial (K := K)) :
    pderiv 0 (flip F) = flip (pderiv 1 F) := by
  have h := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) F
  simpa only [flip, MvPolynomial.renameEquiv_apply, Equiv.swap_apply_right] using h

theorem pderiv_one_flip (F : PlanePolynomial (K := K)) :
    pderiv 1 (flip F) = flip (pderiv 0 F) := by
  have h := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) F
  simpa only [flip, MvPolynomial.renameEquiv_apply, Equiv.swap_apply_left] using h

def flippedPoint (a : Fin 2 → K) : Fin 2 → K := fun i => a (Equiv.swap 0 1 i)

omit [Field K] in
@[simp] theorem flippedPoint_invol (a : Fin 2 → K) : flippedPoint (flippedPoint a) = a := by
  ext i
  fin_cases i <;> simp [flippedPoint]

theorem eval_flip (F : PlanePolynomial (K := K)) (a : Fin 2 → K) :
    eval a (flip F) = eval (flippedPoint a) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, hF]
    congr 1
    fin_cases i <;> simp [flippedPoint]

theorem flip_totalDegree (F : PlanePolynomial (K := K)) : (flip F).totalDegree = F.totalDegree :=
  MvPolynomial.totalDegree_renameEquiv (Equiv.swap (0 : Fin 2) 1) F

theorem flip_irreducible (F : PlanePolynomial (K := K)) : Irreducible (flip F) ↔ Irreducible F :=
  MulEquiv.irreducible_iff (f := (flip (K := K)).toMulEquiv)

theorem flip_affinePolar (p n : ℕ) (F : PlanePolynomial (K := K)) :
    flip (CurveSelfPolarParameter.affinePolar p n F) =
      CurveSelfPolarParameter.affinePolar p n (flip F) := by
  simp only [CurveSelfPolarParameter.affinePolar, map_add, map_mul, map_sub, map_pow,
    flip_C, flip_X_zero, flip_X_one, pderiv_zero_flip, pderiv_one_flip]
  ring

theorem not_self_polar [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (F : PlanePolynomial (K := K)) (hF : Irreducible F)
    (hdeg : F.totalDegree < p) (hnonlinear : 2 ≤ F.totalDegree) :
    ¬ F ∣ CurveSelfPolarParameter.affinePolar p n F := by
  intro hdiv
  obtain ⟨a, ha, i, hai⟩ := CurveSmoothPointExistence.exists_smooth_point_of_degree_lt_char p F hF hdeg
  fin_cases i
  · have hF' : Irreducible (flip F) := (flip_irreducible F).mpr hF
    have hdeg' : (flip F).totalDegree < p := by rwa [flip_totalDegree]
    have hnonlinear' : 2 ≤ (flip F).totalDegree := by rwa [flip_totalDegree]
    have hzero' : eval (flippedPoint a) (flip F) = 0 := by
      rwa [eval_flip, flippedPoint_invol]
    have hY' : eval (flippedPoint a) (pderiv 1 (flip F)) ≠ 0 := by
      rwa [pderiv_one_flip, eval_flip, flippedPoint_invol]
    have hdiv' : flip F ∣ CurveSelfPolarParameter.affinePolar p n (flip F) := by
      rw [← flip_affinePolar]
      exact map_dvd (flip (K := K)).toRingHom hdiv
    exact not_self_polar_at_smooth_point p n (flip F) hF' hdeg' hnonlinear'
      (flippedPoint a) hzero' hY' hdiv'
  · exact not_self_polar_at_smooth_point p n F hF hdeg hnonlinear a ha hai hdiv

end Cylinder.CurveSelfPolarExclusion

end
