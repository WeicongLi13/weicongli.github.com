module

public import Cylinder.ProjectiveChartData
public import Cylinder.HomogeneousCompleteIntersection
public import Cylinder.CompleteIntersectionHilbert
public import Cylinder.ResidualCoordinateTransport
public import Cylinder.ResidualQuotientPieces

/-! The actual affine quotient in an avoiding chart has dimension a*b.
The proof identifies its bounded representatives with a stable homogeneous
quotient piece of the original equations. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.CompleteIntersectionAffineDimension

open Module MvPolynomial Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.CompleteIntersectionKoszul Cylinder.CurvePolarLocal
open Cylinder.CompleteIntersectionGraded Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection

variable {K : Type*} [Field K]

abbrev ChartAlgebra (c : Chart K) (F G : PlaneRing K) :=
  QuotientRing (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))

def chartPieceMap (c : Chart K) (F G : PlaneRing K) (N : ℕ) :
    Forms K N →ₗ[K] ChartAlgebra c F G :=
  ((Ideal.Quotient.mkₐ K _).toLinearMap.comp ResidualQuotientPieces.dehomogenizeLinear).comp
    (c.coordinates.toLinearMap.comp (Forms K N).subtype)

theorem chartPieceMap_kernel (c : Chart K) (F G : PlaneRing K) (e t N : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    LinearMap.ker (chartPieceMap c F G N) = idealPiece F G N := by
  ext H
  change Ideal.Quotient.mk _ (dehomogenize (c.coordinates H.val)) = 0 ↔
    H.val ∈ equationsIdeal F G
  rw [Ideal.Quotient.eq_zero_iff_mem,
    ← homogeneous_mem_iff_dehomogenize_mem (c.coordinates F) (c.coordinates G)
      (c.coordinates H.val) e t N
      (PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb F e hF)
      (PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb G t hG)
      (PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb H.val N H.property)
      hgood.degreeF hgood.degreeG hgood.topF hgood.topcop]
  change H.val ∈ Ideal.comap c.coordinates (equationsIdeal (c.coordinates F) (c.coordinates G)) ↔ _
  rw [ResidualCoordinateTransport.equationsIdeal_comap]

theorem chartPieceMap_surjective (c : Chart K) (F G : PlaneRing K) (e t N : ℕ)
    (he : 0 < e) (ht : 0 < t) (hgood : GoodChart c F G e t) (hN : e + t - 2 ≤ N) :
    Function.Surjective (chartPieceMap c F G N) := by
  intro a
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, hQ, hQP⟩ := AffineFilteredAlgebra.exists_low_degree_representative
    (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G)) e t he ht
    hgood.degreeF hgood.degreeG hgood.topF hgood.topG hgood.topcop P
  let H := homogenize N Q
  have hH : H.IsHomogeneous N := homogenize_homogeneous N Q (hQ.trans hN)
  have hback : (c.coordinates.symm H).IsHomogeneous N :=
    PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb H N hH
  refine ⟨⟨c.coordinates.symm H, hback⟩, ?_⟩
  change Ideal.Quotient.mk _ (dehomogenize (c.coordinates (c.coordinates.symm H))) = _
  rw [AlgEquiv.apply_symm_apply]
  simpa only [H, dehomogenize_homogenize] using hQP

theorem chartAlgebra_finiteDimensional (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hgood : GoodChart c F G e t) :
    FiniteDimensional K (ChartAlgebra c F G) :=
  AffineFilteredAlgebra.quotient_finiteDimensional _ _ e t he ht hgood.degreeF hgood.degreeG
    hgood.topF hgood.topG hgood.topcop

theorem chartAlgebra_finrank (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hgood : GoodChart c F G e t) :
    finrank K (ChartAlgebra c F G) = e * t := by
  let q := chartPieceMap c F G (e + t - 2)
  let E := q.quotKerEquivOfSurjective (chartPieceMap_surjective c F G e t _ he ht hgood le_rfl)
  have hdim := E.finrank_eq
  change finrank K (Forms K (e + t - 2) ⧸ LinearMap.ker (chartPieceMap c F G (e + t - 2))) =
    finrank K (ChartAlgebra c F G) at hdim
  rw [chartPieceMap_kernel c F G e t _ hF hG hgood,
    CompleteIntersectionHilbert.forms_quotient_finrank F G e t _ he ht hF hG hF0 hcop le_rfl] at hdim
  exact hdim.symm

end Cylinder.CompleteIntersectionAffineDimension
end
