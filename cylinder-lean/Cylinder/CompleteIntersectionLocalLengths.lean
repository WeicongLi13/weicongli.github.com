module

public import Cylinder.CompleteIntersectionAffineDimension
public import Cylinder.ArtinianLocalLength

/-! The sum of actual local ring lengths of the affine intersection
algebra in a genuine avoiding chart equals the product of the degrees.
The separate identification with projective structure-sheaf stalks is
not asserted here. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.CompleteIntersectionLocalLengths

open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.CompleteIntersectionAffineDimension

variable {K : Type*} [Field K]

@[instance_reducible] def chartMaximalFintype (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hgood : GoodChart c F G e t) :
    Fintype (MaximalSpectrum (ChartAlgebra c F G)) := by
  letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
  letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
  exact Fintype.ofFinite _

theorem chart_local_lengths [IsAlgClosed K] (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := chartMaximalFintype c F G e t he ht hgood
    ∑ m : MaximalSpectrum (ChartAlgebra c F G),
      Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) =
      (e * t : ℕ∞) := by
  let := chartMaximalFintype c F G e t he ht hgood
  let := chartAlgebra_finiteDimensional c F G e t he ht hgood
  let : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
  rw [ArtinianLocalLength.sum_local_lengths K (ChartAlgebra c F G),
    chartAlgebra_finrank c F G e t he ht hF hG hF0 hcop hgood, Nat.cast_mul]

theorem exists_chart_local_lengths [IsAlgClosed K] (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := chartMaximalFintype c F G e t he ht hgood
      ∑ m : MaximalSpectrum (ChartAlgebra c F G),
        Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) =
        (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, chart_local_lengths c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.CompleteIntersectionLocalLengths
end
