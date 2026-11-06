module

public import Cylinder.ConicAffineNormalForms

/-! Actual root bases put the restriction of a quadratic at infinity in
the secant or tangent form. These are then normalized by verified affine
linear equivalences. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicRootNormalization
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport
open Cylinder.ConicLineCoordinates Cylinder.ConicBinaryRoots Cylinder.ConicAffineMaps
open Cylinder.ConicAffineNormalForms

variable {K : Type*} [Field K]

theorem distinct_roots_transform [Infinite K] (a c e f r s : K) (hrs : r ≠ s) :
    linearPullback (rootCoordinates r s hrs)
      (sixCoefficients a (a * r * s) c (-a * (r + s)) e f) =
      secantForm (-a * (r - s) ^ 2) (e * r + f) (e * s + f) c := by
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval]
  simp [rootCoordinates, rootVector, secantForm, sixCoefficients]
  ring

theorem double_root_transform [Infinite K] (a c e f r : K) :
    linearPullback (doubleRootCoordinates r)
      (sixCoefficients a (a * r * r) c (-a * (r + r)) e f) =
      tangentForm a e (e * r + f) c := by
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval]
  simp [doubleRootCoordinates, tangentForm, sixCoefficients]
  ring

theorem swap_transform [Infinite K] (a b c d e f : K) :
    linearPullback (swapCoordinates (K := K)) (sixCoefficients a b c d e f) =
      sixCoefficients b a c d f e := by
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval]
  simp [swapCoordinates, sixCoefficients]
  ring

theorem normalize_with_nonzero_square [IsAlgClosed K] (a b c d e f : K) (ha : a ≠ 0)
    (hirr : Irreducible (sixCoefficients a b c d e f)) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∃ u : K, u ≠ 0 ∧ (∀ x, g x 2 = x 2) ∧
      (linearPullback g (sixCoefficients a b c d e f) = C u * (X 0 * X 1 - X 2 ^ 2) ∨
        linearPullback g (sixCoefficients a b c d e f) = C u * (X 0 ^ 2 - X 1 * X 2)) := by
  obtain ⟨r, s, hd, hb⟩ := exists_quadratic_roots a d b ha
  rw [hb, hd] at hirr ⊢
  by_cases hrs : r = s
  · subst s
    have ht := pullback_irreducible (doubleRootCoordinates r) _ hirr
    rw [double_root_transform] at ht
    obtain ⟨g, u, hu, hg, hnorm⟩ := normalize_tangent a e (e * r + f) c ha ht
    refine ⟨g.trans (doubleRootCoordinates r), u, hu, ?_, Or.inr ?_⟩
    · intro x
      change doubleRootCoordinates r (g x) 2 = x 2
      rw [doubleRootCoordinates_last, hg]
    · rw [pullback_trans, double_root_transform]
      exact hnorm
  · have hcross : -a * (r - s) ^ 2 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr ha) (pow_ne_zero 2 (sub_ne_zero.mpr hrs))
    have ht := pullback_irreducible (rootCoordinates r s hrs) _ hirr
    rw [distinct_roots_transform] at ht
    obtain ⟨g, u, hu, hg, hnorm⟩ := normalize_secant (-a * (r - s) ^ 2)
      (e * r + f) (e * s + f) c hcross ht
    refine ⟨g.trans (rootCoordinates r s hrs), u, hu, ?_, Or.inl ?_⟩
    · intro x
      change rootCoordinates r s hrs (g x) 2 = x 2
      rw [rootCoordinates_last, hg]
    · rw [pullback_trans, distinct_roots_transform]
      exact hnorm

theorem normalize_coefficients [IsAlgClosed K] (a b c d e f : K)
    (hirr : Irreducible (sixCoefficients a b c d e f)) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∃ u : K, u ≠ 0 ∧ (∀ x, g x 2 = x 2) ∧
      (linearPullback g (sixCoefficients a b c d e f) = C u * (X 0 * X 1 - X 2 ^ 2) ∨
        linearPullback g (sixCoefficients a b c d e f) = C u * (X 0 ^ 2 - X 1 * X 2)) := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · have hd : d ≠ 0 := by
        rcases restriction_coefficients_nonzero a b c d e f hirr with h | h | h
        · exact False.elim (h ha)
        · exact False.elim (h hb)
        · exact h
      have ht : Irreducible (secantForm d e f c) := by
        simpa only [ha, hb, secantForm] using hirr
      obtain ⟨g, u, hu, hg, hnorm⟩ := normalize_secant d e f c hd ht
      refine ⟨g, u, hu, hg, Or.inl ?_⟩
      simpa only [ha, hb, secantForm] using hnorm
    · have ht := pullback_irreducible (swapCoordinates (K := K)) _ hirr
      rw [swap_transform] at ht
      obtain ⟨g, u, hu, hg, hnorm⟩ := normalize_with_nonzero_square b a c d f e hb ht
      refine ⟨g.trans swapCoordinates, u, hu, ?_, ?_⟩
      · intro x
        change swapCoordinates (K := K) (g x) 2 = x 2
        rw [swapCoordinates_last, hg]
      · rw [pullback_trans, swap_transform]
        exact hnorm
  · exact normalize_with_nonzero_square a b c d e f ha hirr

end Cylinder.ConicRootNormalization
end
