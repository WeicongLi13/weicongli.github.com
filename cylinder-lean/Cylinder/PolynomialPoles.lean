module

public import Cylinder.Recurrence
public import Cylinder.PrimeValuation
public import Cylinder.PolynomialDegree
public import Cylinder.HomogeneousDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial conclusions of the common-denominator recurrence

The ring here is the actual three-variable polynomial ring over a field.
The prime valuations, multiplicity bound, and passage from nonnegative
valuations to ring membership are proved in the imported modules.
This file proves the polynomial and homogeneous-degree conclusions of
Proposition `prop:poles`.
-/

@[expose] public section

namespace Cylinder.PolynomialPoles

abbrev Poly (k : Type*) [CommRing k] := MvPolynomial (Fin 3) k

variable {k : Type*} [Field k]
variable {F : Type*} [Field F] [Algebra (Poly k) F] [IsFractionRing (Poly k) F]

/-- The exact finite thresholds in the polynomial ring used by the paper.
`IsInteger` means that there is a polynomial whose image is the given
fraction-field element. -/
theorem finite_common_denominator_polynomial_bounds
    (A : Poly k) (hA : A ≠ 0) (f q : F)
    (num : ℕ → Poly k) (h : ℕ → F) (N : ℕ)
    (hcommon : ∀ n ≤ N, h n = algebraMap (Poly k) F (num n) /
      algebraMap (Poly k) F A)
    (h0 : h 0 = 1) (h1 : h 1 = f)
    (hs : ∀ n, n + 2 ≤ N → h (n + 2) = f * h (n + 1) - q * h n) :
    (A.totalDegree + 2 ≤ N → IsLocalization.IsInteger (Poly k) f) ∧
    (2 * A.totalDegree + 2 ≤ N → IsLocalization.IsInteger (Poly k) q) := by
  have local_bounds (π : Poly k) (hπ : Prime π) :
      (A.totalDegree + 2 ≤ N →
        0 ≤ PrimeValuation.atPrime (Poly k) F π hπ f) ∧
      (2 * A.totalDegree + 2 ≤ N →
        0 ≤ PrimeValuation.atPrime (Poly k) F π hπ q) := by
    let a := multiplicity π A
    have hfinite : FiniteMultiplicity π A := FiniteMultiplicity.of_prime_left hπ hA
    have ha : a ≤ A.totalDegree :=
      PolynomialDegree.prime_power_dvd_degree_bound π A a hπ hA
        (pow_multiplicity_dvd π A)
    have hvalue :
        PrimeValuation.atPrime (Poly k) F π hπ (algebraMap (Poly k) F A) =
          ((a : ℤ) : WithTop ℤ) := by
      rw [PrimeValuation.atPrime_algebraMap, hfinite.emultiplicity_eq_multiplicity]
      exact PrimeValuation.enatToInt_nat a
    have hb := Recurrence.finite_common_denominator_pole_bounds
      (PrimeValuation.atPrime (Poly k) F π hπ)
      (algebraMap (Poly k) F A) f q
      (fun n => algebraMap (Poly k) F (num n)) h a N hvalue
      (fun n _ => PrimeValuation.atPrime_algebraMap_nonnegative (Poly k) F π hπ (num n))
      hcommon h0 h1 hs
    constructor
    · intro hN
      exact hb.1 (by omega)
    · intro hN
      exact hb.2 (by omega)
  constructor
  · intro hN
    apply PrimeValuation.isInteger_of_nonnegative (Poly k) F f
    intro π hπ
    exact (local_bounds π hπ).1 hN
  · intro hN
    apply PrimeValuation.isInteger_of_nonnegative (Poly k) F q
    intro π hπ
    exact (local_bounds π hπ).2 hN

/-- A homogeneous rational function of nonnegative degree is represented
by a ratio of homogeneous polynomials with that degree difference. Its
denominator can differ from the common denominator in the recurrence. -/
def IsHomogeneousFraction (f : F) (d : ℕ) : Prop :=
  ∃ r : ℕ, ∃ D E : Poly k,
    D ≠ 0 ∧ D.IsHomogeneous r ∧ E.IsHomogeneous (r + d) ∧
      f = algebraMap (Poly k) F E / algebraMap (Poly k) F D

/-- After removal of poles, the rational homogeneous degree is the
polynomial homogeneous degree. -/
theorem homogeneous_polynomial_of_integer (f : F) (d : ℕ)
    (hf : IsLocalization.IsInteger (Poly k) f)
    (hh : IsHomogeneousFraction (k := k) f d) :
    ∃ P : Poly k, algebraMap (Poly k) F P = f ∧ P.IsHomogeneous d := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨r, D, E, hD0, hD, hE, hquot⟩ := hh
  have hDmap : algebraMap (Poly k) F D ≠ 0 := by
    intro hz
    apply hD0
    apply IsFractionRing.injective (Poly k) F
    simpa only [map_zero] using hz
  have hprod := (eq_div_iff hDmap).mp (hP.trans hquot)
  have hDE : D * P = E := by
    apply IsFractionRing.injective (Poly k) F
    simpa only [map_mul, mul_comm] using hprod
  exact ⟨P, hP, HomogeneousDivision.quotient_isHomogeneous D E P r d hD0 hD hE hDE⟩

/-- Proposition `prop:poles`, including its homogeneous-degree conclusion.
The original common denominator is only assumed to be nonzero; it need
not be homogeneous. -/
theorem finite_common_denominator_homogeneous_bounds
    (A : Poly k) (hA : A ≠ 0) (f q : F)
    (num : ℕ → Poly k) (h : ℕ → F) (N : ℕ)
    (hcommon : ∀ n ≤ N, h n = algebraMap (Poly k) F (num n) /
      algebraMap (Poly k) F A)
    (h0 : h 0 = 1) (h1 : h 1 = f)
    (hs : ∀ n, n + 2 ≤ N → h (n + 2) = f * h (n + 1) - q * h n)
    (hf : IsHomogeneousFraction (k := k) f 1)
    (hq : IsHomogeneousFraction (k := k) q 2) :
    (A.totalDegree + 2 ≤ N →
      ∃ P : Poly k, algebraMap (Poly k) F P = f ∧ P.IsHomogeneous 1) ∧
    (2 * A.totalDegree + 2 ≤ N →
      ∃ Q : Poly k, algebraMap (Poly k) F Q = q ∧ Q.IsHomogeneous 2) := by
  have hb := finite_common_denominator_polynomial_bounds A hA f q num h N
    hcommon h0 h1 hs
  exact ⟨fun hN => homogeneous_polynomial_of_integer f 1 (hb.1 hN) hf,
    fun hN => homogeneous_polynomial_of_integer q 2 (hb.2 hN) hq⟩

end Cylinder.PolynomialPoles
