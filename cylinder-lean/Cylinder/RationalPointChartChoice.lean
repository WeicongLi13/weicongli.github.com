module

public import Cylinder.ProjectiveIntegerRelations
public import Cylinder.IntegerRepresentativeRelations
public import Cylinder.SimultaneousPlaneLine

/-! Every actual finite projective point set admits a common affine
chart. The original coefficient-relation dimensions do not depend on
the nonzero representative scalings used in that chart. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointChartChoice

open MvPolynomial Module
open Cylinder.ProjectiveChartData Cylinder.PlaneLineCoordinates
open Cylinder.CompleteIntersectionAffinePoints Cylinder.SimultaneousPlaneLine

variable (K : Type*) [Field K]

theorem chartFunctional_lineEquation (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (v : Fin 3 → K) :
    eval v (lineEquation p w) = -w 0 * chartFunctional p w hp hw v := by
  simp only [lineEquation, map_sub, map_mul, eval_C, eval_X]
  change w 1 * (v 1 - p 1 * (p 0)⁻¹ * v 0) -
      w 0 * (v 2 - p 2 * (p 0)⁻¹ * v 0) =
    -w 0 * (v 2 - p 2 * (v 0 / p 0) -
      w 1 * ((v 1 - p 1 * (v 0 / p 0)) / w 0))
  field_simp [hp, hw]
  ring

theorem exists_common_chart [Infinite K] (D : Finset (PlanePointModel.Plane K)) :
    ∃ c : Chart K, ∀ P : D, c.line P.val.rep ≠ 0 := by
  obtain ⟨p, w, hp, _, hw, _, _, _, hav⟩ := exists_simultaneous_line
    (fun j : Empty => nomatch j) (fun j : Empty => nomatch j)
    (fun j : Empty => nomatch j) (fun j : Empty => nomatch j)
    (fun j => nomatch j) (fun j => nomatch j)
    (fun j => nomatch j) (fun j => nomatch j)
    (fun P : D => P.val.rep) (fun P => P.val.rep_nonzero) 1 one_ne_zero
  refine ⟨⟨p, w, hp, hw⟩, fun P hP => ?_⟩
  apply hav P
  rw [chartFunctional_lineEquation K p w hp hw]
  exact mul_eq_zero_of_right _ hP

theorem originalRelations_finrank (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) (v : ℤ) :
    finrank K (ProjectiveIntegerRelations.originalRelations c D v) =
      finrank K (IntegerRepresentativeRelations.integerRelations
        (fun P : D => P.val.rep) v) := by
  let e := IntegerRepresentativeRelations.representativeRelationsEquiv
    (fun P : D => P.val.rep) (fun P => (c.line P.val.rep)⁻¹)
    (fun P => inv_ne_zero (hchart P)) v
  exact e.finrank_eq.symm

end Cylinder.RationalPointChartChoice
end
