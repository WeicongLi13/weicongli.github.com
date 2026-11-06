module

public import Cylinder.LocalRecurrenceClearing
public import Cylinder.PolynomialPoles
public import Mathlib.RingTheory.Localization.FractionRing

/-! The actual point-forced cleared recurrences remove the poles of the
common-denominator rational sequence and produce actual linear and
quadratic numerator quotients. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalCommonDenominator

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PolynomialPoles
open Cylinder.LocalRecurrenceClearing
open scoped Classical

variable {K : Type*} [Field K]

theorem first_field_recurrence (a b₁ b₂ c₀ c₁ c₂ : K) (ha : a ≠ 0)
    (hc : a ^ 2 * c₂ - a * b₁ * c₁ + (b₁ ^ 2 - a * b₂) * c₀ = 0) :
    c₂ / a = (b₁ / a) * (c₁ / a) - ((b₁ / a) ^ 2 - b₂ / a) * (c₀ / a) := by
  field_simp [ha]
  linear_combination hc

theorem second_field_recurrence (a f b₂ c₀ c₁ c₂ : K) (ha : a ≠ 0)
    (hc : a * c₂ - a * f * c₁ + (a * f ^ 2 - b₂) * c₀ = 0) :
    c₂ / a = f * (c₁ / a) - (f ^ 2 - b₂ / a) * (c₀ / a) := by
  field_simp [ha]
  linear_combination hc

abbrev Frac (K : Type*) [Field K] := FractionRing (PlaneRing K)

theorem first_quotient_linear (A : PlaneRing K) (num : ℕ → PlaneRing K) (m : ℕ)
    (hA0 : A ≠ 0) (hA : A.IsHomogeneous m) (hnum0 : num 0 = A)
    (hnum1 : (num 1).IsHomogeneous (m + 1))
    (hclear : ∀ n ≤ m, firstCleared A num n = 0) :
    ∃ f : PlaneRing K, f.IsHomogeneous 1 ∧ num 1 = A * f := by
  let a := algebraMap (PlaneRing K) (Frac K) A
  let h := fun n => algebraMap (PlaneRing K) (Frac K) (num n) / a
  let f := h 1
  let q := f ^ 2 - h 2
  have ha : a ≠ 0 := by
    intro hz
    apply hA0
    apply IsFractionRing.injective (PlaneRing K) (Frac K)
    simpa only [map_zero] using hz
  have h0 : h 0 = 1 := by dsimp [h]; rw [hnum0]; exact div_self ha
  have hrec : ∀ n, n + 2 ≤ m + 2 → h (n + 2) = f * h (n + 1) - q * h n := by
    intro n hn
    have hz := congrArg (algebraMap (PlaneRing K) (Frac K)) (hclear n (by omega))
    simp only [firstCleared, map_add, map_sub, map_mul, map_pow, map_zero] at hz
    exact first_field_recurrence a _ _ _ _ _ ha hz
  have hb := finite_common_denominator_polynomial_bounds A hA0 f q num h (m + 2)
    (fun n hn => rfl) h0 rfl hrec
  have hfInteger : IsLocalization.IsInteger (PlaneRing K) f :=
    hb.1 (by rw [hA.totalDegree hA0])
  have hfHom : IsHomogeneousFraction (k := K) f 1 :=
    ⟨m, A, num 1, hA0, hA, hnum1, rfl⟩
  obtain ⟨P, hP, hPhom⟩ := homogeneous_polynomial_of_integer f 1 hfInteger hfHom
  refine ⟨P, hPhom, ?_⟩
  apply IsFractionRing.injective (PlaneRing K) (Frac K)
  have hp := (eq_div_iff ha).mp hP
  simpa only [map_mul, mul_comm] using hp.symm

theorem second_quotient_quadratic (A f : PlaneRing K) (num : ℕ → PlaneRing K) (m : ℕ)
    (hA0 : A ≠ 0) (hA : A.IsHomogeneous m) (hf : f.IsHomogeneous 1)
    (hnum0 : num 0 = A) (hnum1 : num 1 = A * f) (hnum2 : (num 2).IsHomogeneous (m + 2))
    (hclear : ∀ n ≤ 2 * m, secondCleared A f num n = 0) :
    ∃ g : PlaneRing K, g.IsHomogeneous 2 ∧ num 2 = A * g := by
  let a := algebraMap (PlaneRing K) (Frac K) A
  let f' := algebraMap (PlaneRing K) (Frac K) f
  let h := fun n => algebraMap (PlaneRing K) (Frac K) (num n) / a
  let q := f' ^ 2 - h 2
  have ha : a ≠ 0 := by
    intro hz
    apply hA0
    apply IsFractionRing.injective (PlaneRing K) (Frac K)
    simpa only [map_zero] using hz
  have h0 : h 0 = 1 := by dsimp [h]; rw [hnum0]; exact div_self ha
  have h1 : h 1 = f' := by
    dsimp [h]
    rw [hnum1, map_mul]
    exact mul_div_cancel_left₀ _ ha
  have hrec : ∀ n, n + 2 ≤ 2 * m + 2 → h (n + 2) = f' * h (n + 1) - q * h n := by
    intro n hn
    have hz := congrArg (algebraMap (PlaneRing K) (Frac K)) (hclear n (by omega))
    simp only [secondCleared, map_add, map_sub, map_mul, map_pow, map_zero] at hz
    exact second_field_recurrence a f' _ _ _ _ ha hz
  have hb := finite_common_denominator_polynomial_bounds A hA0 f' q num h (2 * m + 2)
    (fun n hn => rfl) h0 h1 hrec
  have hqInteger : IsLocalization.IsInteger (PlaneRing K) q :=
    hb.2 (by rw [hA.totalDegree hA0])
  have hfh : (f ^ 2).IsHomogeneous 2 := by simpa only [Nat.one_mul] using hf.pow 2
  have hqHom : IsHomogeneousFraction (k := K) q 2 := by
    refine ⟨m, A, A * f ^ 2 - num 2, hA0, hA, (hA.mul hfh).sub hnum2, ?_⟩
    change f' ^ 2 - algebraMap (PlaneRing K) (Frac K) (num 2) / a = _
    rw [map_sub, map_mul, map_pow]
    change f' ^ 2 - algebraMap (PlaneRing K) (Frac K) (num 2) / a =
      (a * f' ^ 2 - algebraMap (PlaneRing K) (Frac K) (num 2)) / a
    field_simp [ha]
  obtain ⟨Q, hQ, hQhom⟩ := homogeneous_polynomial_of_integer q 2 hqInteger hqHom
  refine ⟨f ^ 2 - Q, hfh.sub hQhom, ?_⟩
  apply IsFractionRing.injective (PlaneRing K) (Frac K)
  have hg : algebraMap (PlaneRing K) (Frac K) (f ^ 2 - Q) =
      algebraMap (PlaneRing K) (Frac K) (num 2) / a := by
    rw [map_sub, map_pow, hQ]
    dsimp [q, h, f']
    ring
  have hp := (eq_div_iff ha).mp hg
  simpa only [map_mul, mul_comm] using hp.symm

variable {I : Type*} [Infinite K] [Fintype I]

/-- The geometric point hypotheses produce genuine linear and quadratic
quotients of the actual common numerator polynomials. -/
theorem forms_of_point_numerators (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA0 : A ≠ 0) (hA : A.IsHomogeneous m)
    (hnum0 : num 0 = A) (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i))
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (5 * m + 2) < T.card) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧ num 1 = A * f ∧ num 2 = A * g := by
  obtain ⟨f, hf, hfirst⟩ := first_quotient_linear A num m hA0 hA hnum0 (hnum 1 (by omega))
    (firstCleared_eq_zero F A num e m hF hirr hA hnum hsmall v hv hsep hFzero T h hcommon hrec hcard)
  obtain ⟨g, hg, hsecond⟩ := second_quotient_quadratic A f num m hA0 hA hf hnum0 hfirst
    (hnum 2 (by omega))
    (secondCleared_eq_zero F A f num e m hF hirr hA hf hnum hfirst hsmall v hv hsep hFzero T h hcommon hrec hcard)
  exact ⟨f, g, hf, hg, hfirst, hsecond⟩

#print axioms first_quotient_linear
#print axioms second_quotient_quadratic
#print axioms forms_of_point_numerators

end Cylinder.LocalCommonDenominator

end
