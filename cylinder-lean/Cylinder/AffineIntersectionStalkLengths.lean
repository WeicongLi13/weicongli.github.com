module

public import Cylinder.CompleteIntersectionLocalLengths
public import Cylinder.RingLengthEquiv
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! The local-length formula for actual structure-sheaf stalks of the
affine intersection scheme. The ambient projective-plane identification
is a separate step. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.AffineIntersectionStalkLengths

open AlgebraicGeometry CategoryTheory Module
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.CompleteIntersectionAffineDimension Cylinder.CompleteIntersectionLocalLengths

set_option autoImplicit false

abbrev stalkRing (A : Type*) [CommRing A] (p : PrimeSpectrum A) : CommRingCat :=
  (Spec (CommRingCat.of A)).presheaf.stalk p

def stalkEquiv (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    stalkRing A p ≃+* Localization.AtPrime p.asIdeal :=
  (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv

theorem stalk_length (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    Module.length (stalkRing A p) (stalkRing A p) =
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  RingLengthEquiv.self_length_eq (stalkEquiv A p)

@[instance_reducible] def spectrumFintype (A : Type*) [CommRing A] [IsArtinianRing A]
    [Fintype (MaximalSpectrum A)] : Fintype (PrimeSpectrum A) :=
  Fintype.ofEquiv (MaximalSpectrum A)
    (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := A)).symm

theorem sum_stalk_lengths (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [IsArtinianRing A] [IsAlgClosed K]
    [Fintype (MaximalSpectrum A)] [Fintype (PrimeSpectrum A)] :
    (∑ p : PrimeSpectrum A, Module.length (stalkRing A p) (stalkRing A p)) =
      (finrank K A : ℕ∞) := by
  let e := (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := A)).symm
  rw [← Equiv.sum_comp e]
  simp_rw [stalk_length]
  exact ArtinianLocalLength.sum_local_lengths K A

theorem chart_stalk_lengths {K : Type*} [Field K] [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := chartMaximalFintype c F G e t he ht hgood
    letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
    letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
    letI := spectrumFintype (ChartAlgebra c F G)
    (∑ p : PrimeSpectrum (ChartAlgebra c F G),
      Module.length (stalkRing (ChartAlgebra c F G) p)
        (stalkRing (ChartAlgebra c F G) p)) = (e * t : ℕ∞) := by
  letI := chartMaximalFintype c F G e t he ht hgood
  letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
  letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
  letI := spectrumFintype (ChartAlgebra c F G)
  rw [sum_stalk_lengths K (ChartAlgebra c F G),
    chartAlgebra_finrank c F G e t he ht hF hG hF0 hcop hgood, Nat.cast_mul]

theorem exists_chart_stalk_lengths {K : Type*} [Field K] [IsAlgClosed K]
    (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := chartMaximalFintype c F G e t he ht hgood
      letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
      letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
      letI := spectrumFintype (ChartAlgebra c F G)
      (∑ p : PrimeSpectrum (ChartAlgebra c F G),
        Module.length (stalkRing (ChartAlgebra c F G) p)
          (stalkRing (ChartAlgebra c F G) p)) = (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, chart_stalk_lengths c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.AffineIntersectionStalkLengths

end
