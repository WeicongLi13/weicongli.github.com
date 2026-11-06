module

public import Cylinder.ConicBinaryRoots
public import Cylinder.ConicAffineMaps
public import Cylinder.ConicTernaryQuadratic

/-! Affine normalization of an actual irreducible quadratic after its
restriction at infinity has been put in the two-root or double-root form.
The coefficients needed for invertibility follow from irreducibility. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicAffineNormalForms
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport
open Cylinder.ConicBinaryRoots Cylinder.ConicAffineMaps

variable {K : Type*} [Field K]

def sixCoefficients (a b c d e f : K) : PlaneRing K :=
  C a * X 0 ^ 2 + C b * X 1 ^ 2 + C c * X 2 ^ 2 +
    C d * X 0 * X 1 + C e * X 0 * X 2 + C f * X 1 * X 2

def secantForm (d e f c : K) : PlaneRing K := sixCoefficients 0 0 c d e f
def tangentForm (a e f c : K) : PlaneRing K := sixCoefficients a 0 c 0 e f

theorem restriction_coefficients_nonzero (a b c d e f : K)
    (hirr : Irreducible (sixCoefficients a b c d e f)) : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · by_cases hd : d = 0
      · rw [ha, hb, hd] at hirr
        let R : PlaneRing K := C c * X 2 + C e * X 0 + C f * X 1
        have heq : sixCoefficients 0 0 c 0 e f = X 2 * R := by
          simp only [sixCoefficients, R, map_zero, zero_mul, zero_add, add_zero]
          ring
        have hR0 : R ≠ 0 := by
          intro hz
          exact hirr.ne_zero (by rw [heq, hz, mul_zero])
        have hR : R.IsHomogeneous 1 :=
          ((isHomogeneous_C_mul_X c 2).add (isHomogeneous_C_mul_X e 0)).add
            (isHomogeneous_C_mul_X f 1)
        rcases hirr.isUnit_or_isUnit heq with hX | hRunit
        · exact False.elim (homogeneous_positive_not_isUnit (X 2) 1
            (isHomogeneous_X K 2) (by decide) (X_ne_zero _) hX)
        · exact False.elim (homogeneous_positive_not_isUnit R 1 hR (by decide) hR0 hRunit)
      · exact Or.inr (Or.inr hd)
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

theorem tangent_mixed_coefficient_nonzero [IsAlgClosed K] (a e f c : K) (ha : a ≠ 0)
    (hirr : Irreducible (tangentForm a e f c)) : f ≠ 0 := by
  intro hf
  have heq : tangentForm a e 0 c = C a * X 0 ^ 2 + C e * X 0 * X 2 + C c * X 2 ^ 2 := by
    simp only [tangentForm, sixCoefficients, map_zero, zero_mul, add_zero]
    ring
  rw [hf, heq] at hirr
  exact quadratic_in_two_coordinates_not_irreducible a e c ha 0 2 (by decide) hirr

theorem secant_constant_nonzero [Infinite K] (d e f c : K) (hd : d ≠ 0)
    (hirr : Irreducible (secantForm d e f c)) : c - e * f / d ≠ 0 := by
  intro hz
  have hc : c = e * f / d := sub_eq_zero.mp hz
  let A : PlaneRing K := C d * X 0 + C f * X 2
  let B : PlaneRing K := X 1 + C (e / d) * X 2
  have heq : secantForm d e f c = A * B := by
    apply MvPolynomial.funext
    intro x
    simp [secantForm, sixCoefficients, A, B, hc]
    field_simp [hd]
    ring
  have hA : A.IsHomogeneous 1 := (isHomogeneous_C_mul_X d 0).add (isHomogeneous_C_mul_X f 2)
  have hB : B.IsHomogeneous 1 := (isHomogeneous_X K 1).add (isHomogeneous_C_mul_X (e / d) 2)
  have hA0 : A ≠ 0 := by
    intro hzA
    have h := congrArg (eval ![1, 0, 0]) hzA
    apply hd
    simpa [A] using h
  have hB0 : B ≠ 0 := by
    intro hzB
    have h := congrArg (eval ![0, 1, 0]) hzB
    simp [B] at h
  rcases hirr.isUnit_or_isUnit heq with hunit | hunit
  · exact homogeneous_positive_not_isUnit A 1 hA (by decide) hA0 hunit
  · exact homogeneous_positive_not_isUnit B 1 hB (by decide) hB0 hunit

theorem normalize_secant [Infinite K] (d e f c : K) (hd : d ≠ 0)
    (hirr : Irreducible (secantForm d e f c)) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∃ u : K, u ≠ 0 ∧
      (∀ x, g x 2 = x 2) ∧ linearPullback g (secantForm d e f c) =
        C u * (X 0 * X 1 - X 2 ^ 2) := by
  let κ := c - e * f / d
  have hκ : κ ≠ 0 := secant_constant_nonzero d e f c hd hirr
  let g := affineCoordinates (-κ / d) 1 (-f / d) 0 (-e / d)
    (div_ne_zero (neg_ne_zero.mpr hκ) hd) one_ne_zero
  refine ⟨g, -κ, neg_ne_zero.mpr hκ, fun x => affineCoordinates_last _ _ _ _ _ _ _ x, ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval]
  simp [g, affineCoordinates, affineVector, secantForm, sixCoefficients]
  dsimp only [κ]
  field_simp [hd]
  ring

theorem normalize_tangent [IsAlgClosed K] (a e f c : K) (ha : a ≠ 0)
    (hirr : Irreducible (tangentForm a e f c)) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∃ u : K, u ≠ 0 ∧
      (∀ x, g x 2 = x 2) ∧ linearPullback g (tangentForm a e f c) =
        C u * (X 0 ^ 2 - X 1 * X 2) := by
  have hf := tangent_mixed_coefficient_nonzero a e f c ha hirr
  let g := affineCoordinates 1 (-a / f) 0 (-e / f) (-c / f)
    one_ne_zero (div_ne_zero (neg_ne_zero.mpr ha) hf)
  refine ⟨g, a, ha, fun x => affineCoordinates_last _ _ _ _ _ _ _ x, ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval]
  simp [g, affineCoordinates, affineVector, tangentForm, sixCoefficients]
  field_simp [hf]
  ring

end Cylinder.ConicAffineNormalForms
end
