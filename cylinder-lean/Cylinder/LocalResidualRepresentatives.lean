module

public import Cylinder.ProjectivePointIdealTransport
public import Cylinder.IntegerResidualMultiplication
public import Cylinder.ResidualCoordinateMultiplication
public import Cylinder.CompleteIntersectionLowPieces
public import Cylinder.PlaneRelationSpaces
public import Cylinder.ProjectiveIntegerRelations
public import Cylinder.ProjectiveDualityMultiplication

/-!
Low-degree residual representatives for the original projective equations.
The chart is selected from the actual coprime complete intersection, and
the isomorphism uses the already constructed single residue functional.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalResidualRepresentatives

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.ProjectiveChartData Cylinder.ProjectivePointIdealTransport
open Cylinder.PlaneLineCoordinates Cylinder.CurvePolarLocal Cylinder.FiniteEvaluationDuality
open Cylinder.CompleteIntersectionKoszul Cylinder.ResidualEvaluation
open Cylinder.ResidualIntegerPieces Cylinder.PlaneRelationSpaces

variable {K : Type*} [Field K]

local instance : GradedAlgebra (HomogeneousCompleteIntersection.HomForms K) := MvPolynomial.gradedAlgebra

abbrev ResidualIdeal (F G : PlaneRing K) (D : Finset (PlanePointModel.Plane K)) :=
  (equationsIdeal F G).colon (originalPointIdeal D : Set (PlaneRing K))

abbrev OriginalQuotient (F G : PlaneRing K) (D : Finset (PlanePointModel.Plane K)) (n : ℤ) :=
  ResidualCoordinateTransport.ResidualQuotient (equationsIdeal F G) (originalPointIdeal D)
    (integerPlaneForms K) n

theorem normalized_relationSpace_eq (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (j : ℕ) :
    relationSpace (fun P : D => c.normalizedPoint P.val) j =
      IntegerEvaluationDuality.integerCoefficientRelations (fun P : D => c.affinePoint P.val) (j : ℤ) := by
  simpa only [ProjectiveIntegerRelations.originalRelations, Int.natCast_nonneg,
    ite_true, Int.toNat_natCast] using ProjectiveIntegerRelations.originalRelations_eq c D hchart (j : ℤ)

def validChartSystem (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
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

def coordinateQuotientEquiv (c : Chart K) (F G : PlaneRing K)
    (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (n : ℤ) :
    OriginalQuotient F G D n ≃ₗ[K]
      IntegerResidualQuotient (c.coordinates F) (c.coordinates G)
        (fun P : D => c.affinePoint P.val) n :=
  ResidualCoordinateTransport.residualQuotientEquiv c.coordinates
    (equationsIdeal F G) (originalPointIdeal D)
    (equationsIdeal (c.coordinates F) (c.coordinates G))
    (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal
    (integerPlaneForms K) (integerForms K) n
    (ResidualCoordinateTransport.equationsIdeal_comap c.coordinates F G)
    (pointIdeal_comap c D hchart) (integerForms_comap c n)

def lowDegreeRelationEquiv (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (j n : ℕ) (hdegree : (e : ℤ) + t - 3 - j = n)
    (hne : n < e) (hnt : n < t) :
    relationSpace (fun P : D => c.normalizedPoint P.val) j ≃ₗ[K]
      Cylinder.PlanePlateau.piece (ResidualIdeal F G D) n := by
  let hchart := point_line_ne_zero c F G e t hgood D hpoints
  let E := (LinearEquiv.ofEq _ _ (normalized_relationSpace_eq c D hchart j)).trans
    (IntegerResidualDuality.relationResidualEquiv (c.coordinates F) (c.coordinates G) e t
      (fun P : D => c.affinePoint P.val)
      (validChartSystem c F G e t he ht hF hG hgood D hpoints) (j : ℤ))
  have ER : relationSpace (fun P : D => c.normalizedPoint P.val) j ≃ₗ[K]
      OriginalQuotient F G D (n : ℤ) := by
    rw [← hdegree]
    exact E.trans (coordinateQuotientEquiv c F G D hchart _).symm
  exact ER.trans (CompleteIntersectionLowPieces.relativePieceEquiv F G (originalPointIdeal D)
    e t n hF hG hne hnt)

theorem relation_finrank_eq_residual_piece (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (j n : ℕ) (hdegree : (e : ℤ) + t - 3 - j = n)
    (hne : n < e) (hnt : n < t) :
    finrank K (relationSpace (fun P : D => c.normalizedPoint P.val) j) =
      finrank K (Cylinder.PlanePlateau.piece (ResidualIdeal F G D) n) :=
  (lowDegreeRelationEquiv c F G e t he ht hF hG hgood D hpoints j n hdegree hne hnt).finrank_eq

theorem exists_low_degree_chart [Infinite K] (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G)
    (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) :
    ∃ c : Chart K, c.line ≠ 0 ∧ (∀ P : D, c.line (c.normalizedPoint P.val) = 1) ∧
      GoodChart c F G e t ∧
      ∀ j n : ℕ, (e : ℤ) + t - 3 - j = n → n < e → n < t →
        Nonempty (relationSpace (fun P : D => c.normalizedPoint P.val) j ≃ₗ[K]
          Cylinder.PlanePlateau.piece (ResidualIdeal F G D) n) := by
  obtain ⟨c, hgood⟩ := exists_goodChart F G e t he ht hF hG hF0 hG0 hcop
  have hchart := point_line_ne_zero c F G e t hgood D hpoints
  refine ⟨c, line_ne_zero c, fun P => normalizedPoint_line c P.val (hchart P), hgood, ?_⟩
  intro j n hdegree hne hnt
  exact ⟨lowDegreeRelationEquiv c F G e t he ht hF hG hgood D hpoints j n hdegree hne hnt⟩

end Cylinder.LocalResidualRepresentatives

end
