module

public import Cylinder.ProjectivePointIdealTransport
public import Cylinder.PlaneRelationSpaces
public import Cylinder.IntegerEvaluationDuality

/-! The original normalized projective coefficient relations in all integer degrees. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveIntegerRelations

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.PlaneLineCoordinates Cylinder.PlaneRelationSpaces Cylinder.FiniteEvaluationDuality
open Cylinder.IntegerEvaluationDuality

variable {K : Type*} [Field K]

def originalRelations (c : Chart K) (D : Finset (PlanePointModel.Plane K)) (j : ℤ) :
    Submodule K (D → K) :=
  if 0 ≤ j then relationSpace (fun P : D => c.normalizedPoint P.val) j.toNat else ⊤

theorem originalRelations_eq (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (j : ℤ) :
    originalRelations c D j = integerCoefficientRelations (fun P : D => c.affinePoint P.val) j := by
  by_cases hj : 0 ≤ j
  · ext a
    simp only [originalRelations, integerCoefficientRelations, if_pos hj]
    rw [mem_relationSpace, mem_coefficientRelations_iff_homogeneous]
    constructor
    · intro h H hH
      let Q := c.coordinates.symm H
      have hQ := PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb H j.toNat hH
      have hsum := h Q hQ
      have heval : ∀ P : D,
          eval (normalizedPoints (fun P : D => c.affinePoint P.val) P) H =
            eval (c.normalizedPoint P.val) Q := by
        intro P
        have he := eval_normalized_coordinates c P.val (hchart P) Q j.toNat hQ
        change eval (fun x : Option (Fin 2) => x.elim 1 (c.affinePoint P.val)) (c.coordinates Q) =
          eval (c.normalizedPoint P.val) Q at he
        change eval (fun x : Option (Fin 2) => x.elim 1 (c.affinePoint P.val)) H =
          eval (c.normalizedPoint P.val) Q
        simpa only [Q, AlgEquiv.apply_symm_apply] using he
      simpa only [heval] using hsum
    · intro h H hH
      have hphi := chartCoordinates_homogeneous c.a c.b c.ha c.hb H j.toNat hH
      have hsum := h (c.coordinates H) hphi
      have heval : ∀ P : D,
          eval (normalizedPoints (fun P : D => c.affinePoint P.val) P) (c.coordinates H) =
            eval (c.normalizedPoint P.val) H :=
        fun P => eval_normalized_coordinates c P.val (hchart P) H j.toNat hH
      simpa only [heval] using hsum
  · simp only [originalRelations, integerCoefficientRelations, if_neg hj]

def originalRelationsEquiv (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (j : ℤ) :
    originalRelations c D j ≃ₗ[K] integerCoefficientRelations (fun P : D => c.affinePoint P.val) j :=
  LinearEquiv.ofEq _ _ (originalRelations_eq c D hchart j)

end Cylinder.ProjectiveIntegerRelations

end
