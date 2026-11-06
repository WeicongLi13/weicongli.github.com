module

public import Cylinder.ProjectiveCoordinateIso
public import Cylinder.ProjectiveSchemeBezout

/-! The actual coordinate isomorphism carries germs of homogeneous
fractions to the corresponding homogeneous-fraction germs. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.OriginalProjectiveGerms

open MvPolynomial AlgebraicGeometry CategoryTheory
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.ProjectiveCoordinateIso Cylinder.ProjectiveChartData
open Cylinder.HilbertEvaluation Cylinder.CurvePolarLocal Cylinder.ProjectiveEquationGerms

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def chartLinearForm (c : Chart K) : PlaneRing K := c.coordinates.symm (X none)

theorem chartLinearForm_mem (c : Chart K) : chartLinearForm K c ∈ originalGrading K 1 :=
  (backward c).map_mem (coordinate_mem K)

theorem chartLinearForm_image (c : Chart K) : (forward c) (chartLinearForm K c) = X none :=
  c.coordinates.apply_symm_apply _

def originalFractionGerm (L : PlaneRing K) (hL : L ∈ originalGrading K 1)
    (q : originalPlane K) (hq : q ∈ Proj.basicOpen (originalGrading K) L) (n : ℕ)
    (H : PlaneRing K) (hH : H ∈ originalGrading K (n • (1 : ℕ))) :
    (originalPlane K).presheaf.stalk q :=
  (originalPlane K).presheaf.germ (Proj.basicOpen (originalGrading K) L) q hq
    (Proj.awayToSection (originalGrading K) L
      (HomogeneousLocalization.Away.mk (originalGrading K) hL n H hH))

def targetFractionGerm (L : HomogeneousPlanePolynomial (K := K)) (hL : L ∈ grading K 1)
    (q : projectivePlane K) (hq : q ∈ Proj.basicOpen (grading K) L) (n : ℕ)
    (H : HomogeneousPlanePolynomial (K := K)) (hH : H ∈ grading K (n • (1 : ℕ))) :
    (projectivePlane K).presheaf.stalk q :=
  (projectivePlane K).presheaf.germ (Proj.basicOpen (grading K) L) q hq
    (Proj.awayToSection (grading K) L
      (HomogeneousLocalization.Away.mk (grading K) hL n H hH))

theorem fractionGerm_map (c : Chart K) (L : PlaneRing K) (hL : L ∈ originalGrading K 1)
    (q : projectivePlane K) (hq : q ∈ Proj.basicOpen (grading K) ((forward c) L))
    (n : ℕ) (H : PlaneRing K) (hH : H ∈ originalGrading K (n • (1 : ℕ))) :
    stalkEquiv c q
      (originalFractionGerm K L hL ((coordinateIso c).hom q) hq n H hH) =
      targetFractionGerm K ((forward c) L) ((forward c).map_mem hL) q hq
        n ((forward c) H) ((forward c).map_mem hH) := by
  rw [ProjectiveCoordinateIso.stalkEquiv_apply]
  unfold originalFractionGerm targetFractionGerm
  change (Proj.map (forward c) (irrelevant_forward c)).stalkMap q
    ((originalPlane K).presheaf.germ (Proj.basicOpen (originalGrading K) L)
      ((Proj.map (forward c) (irrelevant_forward c)) q) hq _) = _
  rw [germ_stalkMap_appLE _ _ (Proj.basicOpen (grading K) ((forward c) L)) le_rfl q hq]
  have hs := congrArg
    (fun u => u (HomogeneousLocalization.Away.mk (originalGrading K) hL n H hH))
    (Proj.awayToSection_comp_appLE (forward c) (irrelevant_forward c) hL)
  change (Proj.map (forward c) (irrelevant_forward c)).appLE
      (Proj.basicOpen (originalGrading K) L) (Proj.basicOpen (grading K) ((forward c) L)) le_rfl
      (Proj.awayToSection (originalGrading K) L
        (HomogeneousLocalization.Away.mk (originalGrading K) hL n H hH)) =
    Proj.awayToSection (grading K) ((forward c) L)
      (HomogeneousLocalization.Away.map (forward c) L
        (HomogeneousLocalization.Away.mk (originalGrading K) hL n H hH)) at hs
  rw [hs, HomogeneousLocalization.Away.map_mk]

theorem chart_point_mem (c : Chart K) (q : projectivePlane K) (hq : q ∈ standardOpen K) :
    (coordinateIso c).hom q ∈ Proj.basicOpen (originalGrading K) (chartLinearForm K c) := by
  change chartLinearForm K c ∉ ((coordinateIso c).hom q).asHomogeneousIdeal
  rw [membership]
  change (forward c) (chartLinearForm K c) ∉ q.asHomogeneousIdeal
  rw [chartLinearForm_image]
  exact hq

theorem targetFractionGerm_eq_standard [Infinite K]
    (L : HomogeneousPlanePolynomial (K := K)) (hL : L ∈ grading K 1) (hZ : L = X none)
    (q : projectivePlane K) (hq : q ∈ Proj.basicOpen (grading K) L)
    (n : ℕ) (H : HomogeneousPlanePolynomial (K := K)) (hH : H ∈ grading K (n • (1 : ℕ))) :
    targetFractionGerm K L hL q hq n H hH =
      ProjectiveSchemeBezout.fractionGerm K q (by simpa only [hZ] using hq) n H hH := by
  subst L
  rfl

theorem chart_fractionGerm_map [Infinite K] (c : Chart K)
    (q : projectivePlane K) (hq : q ∈ standardOpen K)
    (n : ℕ) (H : PlaneRing K) (hH : H.IsHomogeneous n) :
    stalkEquiv c q
      (originalFractionGerm K (chartLinearForm K c) (chartLinearForm_mem K c)
        ((coordinateIso c).hom q) (chart_point_mem K c q hq) n H (by simpa using hH)) =
      ProjectiveSchemeBezout.fractionGerm K q hq n (c.coordinates H)
        (ProjectiveSchemeBezout.coordinates_mem K c H n hH) := by
  have hh : H ∈ originalGrading K (n • (1 : ℕ)) := by simpa using hH
  have hq' : q ∈ Proj.basicOpen (grading K) ((forward c) (chartLinearForm K c)) := by
    rw [chartLinearForm_image]
    exact hq
  calc
    _ = targetFractionGerm K ((forward c) (chartLinearForm K c))
        ((forward c).map_mem (chartLinearForm_mem K c)) q hq' n ((forward c) H)
        ((forward c).map_mem hh) :=
      fractionGerm_map K c (chartLinearForm K c) (chartLinearForm_mem K c) q hq' n H hh
    _ = _ := targetFractionGerm_eq_standard K _ _ (chartLinearForm_image K c) q hq' n _ _

end Cylinder.OriginalProjectiveGerms
end
