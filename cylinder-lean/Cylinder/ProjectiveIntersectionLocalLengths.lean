module

public import Cylinder.ProjectiveIntersectionPoints
public import Cylinder.AffineIntersectionLocalRings
public import Cylinder.CompleteIntersectionLocalLengths

/-! The local intersection lengths at the original projective common
zeros sum to the product of degrees. Each local term is the actual
localized affine polynomial ring modulo the dehomogenized equations in
a genuine avoiding chart. A literal Proj-stalk identification remains
separate from this algebraic formulation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

namespace Cylinder.ProjectiveIntersectionLocalLengths

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.CurvePolarLocal Cylinder.ProjectiveIntersectionPoints
open Cylinder.AffineIntersectionPoints Cylinder.AffineIntersectionLocalRings
open Cylinder.CompleteIntersectionAffineDimension Cylinder.CompleteIntersectionLocalLengths

variable {K : Type*} [Field K]

def localIntersectionLength (c : Chart K) (F G : PlaneRing K) (P : ProjectiveCommonZero F G) : ℕ∞ :=
  Module.length (PointLocal (c.affinePoint P.val))
    (LocalIntersectionQuotient (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))
      (c.affinePoint P.val))

@[instance_reducible] def projectiveCommonZeroFintype [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Fintype (ProjectiveCommonZero F G) := by
  letI := chartMaximalFintype c F G e t he ht hgood
  exact Fintype.ofEquiv (MaximalSpectrum (ChartAlgebra c F G))
    (projectiveCommonZeroEquivMaximalSpectrum c F G e t he ht hF hG hgood).symm

theorem localIntersectionLength_eq [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t)
    (P : ProjectiveCommonZero F G) :
    localIntersectionLength c F G P =
      Module.length (Localization.AtPrime
        (projectiveCommonZeroEquivMaximalSpectrum c F G e t he ht hF hG hgood P).asIdeal)
        (Localization.AtPrime
        (projectiveCommonZeroEquivMaximalSpectrum c F G e t he ht hF hG hgood P).asIdeal) :=
  local_intersection_length (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))
    (toAffine c F G e t hF hG hgood P)

theorem sum_projective_local_lengths [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
    ∑ P : ProjectiveCommonZero F G, localIntersectionLength c F G P = (e * t : ℕ∞) := by
  let := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  let := chartMaximalFintype c F G e t he ht hgood
  let E := projectiveCommonZeroEquivMaximalSpectrum c F G e t he ht hF hG hgood
  calc
    _ = ∑ P : ProjectiveCommonZero F G,
        Module.length (Localization.AtPrime (E P).asIdeal) (Localization.AtPrime (E P).asIdeal) := by
      apply Finset.sum_congr rfl
      intro P _
      exact localIntersectionLength_eq c F G e t he ht hF hG hgood P
    _ = ∑ m : MaximalSpectrum (ChartAlgebra c F G),
        Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal) :=
      E.sum_comp (fun m => Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal))
    _ = _ := chart_local_lengths c F G e t he ht hF hG hF0 hcop hgood

theorem exists_projective_local_length_formula [IsAlgClosed K]
    (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) :
    ∃ c : Chart K, ∃ hgood : GoodChart c F G e t,
      letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
      ∑ P : ProjectiveCommonZero F G, localIntersectionLength c F G P = (e * t : ℕ∞) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  exact ⟨c, hgood, sum_projective_local_lengths c F G e t he ht hF hG hF0 hcop hgood⟩

end Cylinder.ProjectiveIntersectionLocalLengths
end
