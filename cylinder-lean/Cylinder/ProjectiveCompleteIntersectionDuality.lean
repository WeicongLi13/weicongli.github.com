module

public import Cylinder.ProjectiveIntegerRelations
public import Cylinder.IntegerResidualDuality
public import Cylinder.ResidualCoordinateTransport

/-! Complete-intersection duality for the original projective equations and points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveCompleteIntersectionDuality

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.ProjectivePointIdealTransport Cylinder.ProjectiveIntegerRelations
open Cylinder.PlaneLineCoordinates Cylinder.CurvePolarLocal
open Cylinder.CompleteIntersectionKoszul Cylinder.ResidualEvaluation
open Cylinder.ResidualIntegerPieces

variable {K : Type*} [Field K]

local instance : GradedAlgebra (HomogeneousCompleteIntersection.HomForms K) := MvPolynomial.gradedAlgebra

abbrev OriginalResidualQuotient (F G : PlaneRing K) (D : Finset (PlanePointModel.Plane K)) (d : ℤ) :=
  ResidualCoordinateTransport.ResidualQuotient (equationsIdeal F G) (originalPointIdeal D)
    (integerPlaneForms K) d

def coordinateResidualEquiv (c : Chart K) (F G : PlaneRing K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (d : ℤ) :
    OriginalResidualQuotient F G D d ≃ₗ[K]
      IntegerResidualQuotient (c.coordinates F) (c.coordinates G) (fun P : D => c.affinePoint P.val) d :=
  ResidualCoordinateTransport.residualQuotientEquiv c.coordinates
    (equationsIdeal F G) (originalPointIdeal D)
    (equationsIdeal (c.coordinates F) (c.coordinates G))
    (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal
    (integerPlaneForms K) (integerForms K) d
    (ResidualCoordinateTransport.equationsIdeal_comap c.coordinates F G)
    (pointIdeal_comap c D hchart) (integerForms_comap c d)

theorem chartValidSystem (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) :
    IntegerResidualDuality.ValidSystem (c.coordinates F) (c.coordinates G) e t
      (fun P : D => c.affinePoint P.val) :=
  let hchart := point_line_ne_zero c F G e t hgood D hpoints
  let hzeros := affinePoints_common_zero c F G e t hF hG hgood D hpoints
  ⟨he, ht, chartCoordinates_homogeneous c.a c.b c.ha c.hb F e hF,
    chartCoordinates_homogeneous c.a c.b c.ha c.hb G t hG,
    hgood.degreeF, hgood.degreeG, hgood.topF, hgood.topG, hgood.topcop,
    affinePoints_injective c D hchart, hzeros.1, hzeros.2⟩

/-- Every integer relation degree is sent to the actual residual quotient
of the original equations, with no chart-coprimality assumption left over. -/
def projectiveRelationResidualEquiv (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) (j : ℤ) :
    originalRelations c D j ≃ₗ[K] OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j) :=
  let hchart := point_line_ne_zero c F G e t hgood D hpoints
  (originalRelationsEquiv c D hchart j).trans
    ((IntegerResidualDuality.relationResidualEquiv (c.coordinates F) (c.coordinates G) e t
      (fun P : D => c.affinePoint P.val) (chartValidSystem c F G e t he ht hF hG hgood D hpoints) j).trans
      (coordinateResidualEquiv c F G D hchart _).symm)

theorem exists_projective_duality [Infinite K] (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) :
    ∃ c : Chart K, c.line ≠ 0 ∧ (∀ P : D, c.line (c.normalizedPoint P.val) = 1) ∧
      Nonempty (∀ j : ℤ, originalRelations c D j ≃ₗ[K]
        OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j)) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  have hchart := point_line_ne_zero c F G e t hgood D hpoints
  exact ⟨c, line_ne_zero c, fun P => normalizedPoint_line c P.val (hchart P),
    ⟨fun j => projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j⟩⟩

end Cylinder.ProjectiveCompleteIntersectionDuality

end
