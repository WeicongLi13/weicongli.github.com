module

public import Cylinder.ProjectiveCompleteIntersectionDuality
public import Cylinder.IntegerResidualMultiplication
public import Cylinder.ResidualCoordinateMultiplication

/-! Actual multiplication compatibility for the original projective residual ideals. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveDualityMultiplication

open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.ProjectivePointIdealTransport Cylinder.ProjectiveIntegerRelations
open Cylinder.ProjectiveCompleteIntersectionDuality Cylinder.PlaneLineCoordinates
open Cylinder.CurvePolarLocal Cylinder.CompleteIntersectionKoszul Cylinder.ResidualEvaluation
open Cylinder.ResidualIntegerPieces Cylinder.ResidualCoordinateTransport

variable {K : Type*} [Field K]

local instance : GradedAlgebra (HomogeneousCompleteIntersection.HomForms K) := MvPolynomial.gradedAlgebra

theorem integerForms_left_mul (d m : ℤ) (u : ℕ) (hm : d + u = m)
    (Q : HomogeneousCompleteIntersection.HomRing (K := K)) (hQ : Q.IsHomogeneous u) :
    ∀ H ∈ integerForms K d, Q * H ∈ integerForms K m := by
  intro H hH
  rw [mul_comm]
  exact IntegerResidualMultiplication.integerForms_mul H Q d m u hm hH hQ

theorem integerPlaneForms_left_mul (c : Chart K) (d m : ℤ) (u : ℕ) (hm : d + u = m)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) :
    ∀ H ∈ integerPlaneForms K d, Q * H ∈ integerPlaneForms K m := by
  intro H hH
  apply (integerForms_comap c m).ge
  change c.coordinates (Q * H) ∈ integerForms K m
  rw [map_mul]
  exact integerForms_left_mul d m u hm (c.coordinates Q)
    (chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ) _ ((integerForms_comap c d).le hH)

def originalResidualMultiplication (c : Chart K) (F G : PlaneRing K)
    (D : Finset (PlanePointModel.Plane K)) (d m : ℤ) (u : ℕ) (hm : d + u = m)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) :
    OriginalResidualQuotient F G D d →ₗ[K] OriginalResidualQuotient F G D m :=
  ResidualCoordinateMultiplication.residualMultiplication (equationsIdeal F G) (originalPointIdeal D)
    (integerPlaneForms K) d m Q (integerPlaneForms_left_mul c d m u hm Q hQ)

theorem targetMultiplication_eq {I : Type*} [Fintype I]
    (F G : HomogeneousCompleteIntersection.HomRing (K := K)) (v : I → Fin 2 → K) (d m : ℤ) (u : ℕ)
    (hm : d + u = m) (Q : HomogeneousCompleteIntersection.HomRing (K := K)) (hQ : Q.IsHomogeneous u) :
    ResidualCoordinateMultiplication.residualMultiplication (equationsIdeal F G)
      (homogeneousPointIdeal v).toIdeal (integerForms K) d m Q (integerForms_left_mul d m u hm Q hQ) =
      IntegerResidualMultiplication.integerResidualMultiplication F G v d m u hm Q hQ := by
  apply LinearMap.ext
  intro a
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (integerEquationPiece F G v d) a
  change Submodule.Quotient.mk
      (ResidualCoordinateMultiplication.residualPieceMultiplication (equationsIdeal F G)
        (homogeneousPointIdeal v).toIdeal (integerForms K) d m Q (integerForms_left_mul d m u hm Q hQ) H) =
    Submodule.Quotient.mk (IntegerResidualMultiplication.integerPieceMultiplication F G v d m u hm Q hQ H)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact mul_comm Q H.val

theorem coordinateResidual_multiply (c : Chart K) (F G : PlaneRing K)
    (D : Finset (PlanePointModel.Plane K)) (hchart : ∀ P : D, c.line P.val.rep ≠ 0)
    (d m : ℤ) (u : ℕ) (hm : d + u = m) (Q : PlaneRing K) (hQ : Q.IsHomogeneous u)
    (a : OriginalResidualQuotient F G D d) :
    coordinateResidualEquiv c F G D hchart m (originalResidualMultiplication c F G D d m u hm Q hQ a) =
      IntegerResidualMultiplication.integerResidualMultiplication (c.coordinates F) (c.coordinates G)
        (fun P : D => c.affinePoint P.val) d m u hm (c.coordinates Q)
        (chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ)
        (coordinateResidualEquiv c F G D hchart d a) := by
  have hphi := chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ
  have h := ResidualCoordinateMultiplication.coordinateQuotientEquiv_multiply c.coordinates
    (equationsIdeal F G) (originalPointIdeal D)
    (equationsIdeal (c.coordinates F) (c.coordinates G))
    (homogeneousPointIdeal (fun P : D => c.affinePoint P.val)).toIdeal
    (integerPlaneForms K) (integerForms K) d m
    (ResidualCoordinateTransport.equationsIdeal_comap c.coordinates F G)
    (pointIdeal_comap c D hchart) (integerForms_comap c d) (integerForms_comap c m) Q
    (integerPlaneForms_left_mul c d m u hm Q hQ)
    (integerForms_left_mul d m u hm (c.coordinates Q) hphi) a
  rw [targetMultiplication_eq _ _ _ d m u hm (c.coordinates Q) hphi] at h
  exact h

def originalCoefficientMultiplication (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (j : ℤ) (u : ℕ)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) :
    originalRelations c D j →ₗ[K] originalRelations c D (j - u) :=
  (originalRelationsEquiv c D hchart (j - u)).symm.toLinearMap.comp
    ((IntegerResidualMultiplication.integerCoefficientMultiplication (fun P : D => c.affinePoint P.val)
      j u (c.coordinates Q) (chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ)).comp
      (originalRelationsEquiv c D hchart j).toLinearMap)

theorem originalCoefficientMultiplication_apply (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (j : ℤ) (u : ℕ)
    (Q : PlaneRing K) (hQ : Q.IsHomogeneous u) (a : originalRelations c D j) (P : D) :
    (originalCoefficientMultiplication c D hchart j u Q hQ a).val P =
      a.val P * eval (c.normalizedPoint P.val) Q := by
  change a.val P * eval (Cylinder.FiniteEvaluationDuality.normalizedPoints
    (fun P : D => c.affinePoint P.val) P) (c.coordinates Q) = _
  have he := eval_normalized_coordinates c P.val (hchart P) Q u hQ
  change eval (fun x : Option (Fin 2) => x.elim 1 (c.affinePoint P.val)) (c.coordinates Q) =
    eval (c.normalizedPoint P.val) Q at he
  change a.val P * eval (fun x : Option (Fin 2) => x.elim 1 (c.affinePoint P.val)) (c.coordinates Q) = _
  exact congrArg (fun z => a.val P * z) he

/-- The original relation/residual maps commute with multiplication by every
actual homogeneous form, in all integer relation degrees. -/
theorem projective_duality_multiply (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (j : ℤ) (u : ℕ) (Q : PlaneRing K) (hQ : Q.IsHomogeneous u)
    (a : OriginalResidualQuotient F G D ((e : ℤ) + t - 3 - j)) :
    (projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints (j - u)).symm
      (originalResidualMultiplication c F G D _ _ u (by ring) Q hQ a) =
    originalCoefficientMultiplication c D (point_line_ne_zero c F G e t hgood D hpoints)
      j u Q hQ ((projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints j).symm a) := by
  let hchart := point_line_ne_zero c F G e t hgood D hpoints
  apply (originalRelationsEquiv c D hchart (j - u)).injective
  change (IntegerResidualDuality.relationResidualEquiv (c.coordinates F) (c.coordinates G) e t
      (fun P : D => c.affinePoint P.val) (chartValidSystem c F G e t he ht hF hG hgood D hpoints) (j - u)).symm
    (coordinateResidualEquiv c F G D hchart _
      (originalResidualMultiplication c F G D _ _ u (by ring) Q hQ a)) =
    IntegerResidualMultiplication.integerCoefficientMultiplication (fun P : D => c.affinePoint P.val)
      j u (c.coordinates Q) (chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ)
      ((IntegerResidualDuality.relationResidualEquiv (c.coordinates F) (c.coordinates G) e t
        (fun P : D => c.affinePoint P.val) (chartValidSystem c F G e t he ht hF hG hgood D hpoints) j).symm
        (coordinateResidualEquiv c F G D hchart _ a))
  rw [coordinateResidual_multiply c F G D hchart _ _ u (by ring) Q hQ a]
  exact IntegerResidualMultiplication.duality_multiply (c.coordinates F) (c.coordinates G) e t
    (fun P : D => c.affinePoint P.val) (chartValidSystem c F G e t he ht hF hG hgood D hpoints)
    j u (c.coordinates Q) (chartCoordinates_homogeneous c.a c.b c.ha c.hb Q u hQ)
    (coordinateResidualEquiv c F G D hchart _ a)

end Cylinder.ProjectiveDualityMultiplication

end
