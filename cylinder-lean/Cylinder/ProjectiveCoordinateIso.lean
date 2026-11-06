module

public import Cylinder.ProjectiveAffineOpen
public import Cylinder.ProjectiveChartData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! The selected linear coordinates induce an isomorphism of the actual
projective schemes and of their structure-sheaf stalks. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.ProjectiveCoordinateIso

open AlgebraicGeometry CategoryTheory MvPolynomial
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveChartData
open Cylinder.ProjectiveAffineOpen
open Cylinder.HilbertEvaluation Cylinder.PlaneLineCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

abbrev originalGrading (K : Type*) [Field K] := homogeneousSubmodule (Fin 3) K
abbrev originalPlane (K : Type*) [Field K] := Proj (originalGrading K)

def forward (c : Chart K) : originalGrading K →+*ᵍ grading K where
  __ := c.coordinates.toRingEquiv.toRingHom
  map_mem {i} {H} hH := chartCoordinates_homogeneous c.a c.b c.ha c.hb H i hH

def backward (c : Chart K) : grading K →+*ᵍ originalGrading K where
  __ := c.coordinates.symm.toRingEquiv.toRingHom
  map_mem {i} {H} hH :=
    PlaneCoordinateInverse.chartCoordinates_symm_homogeneous c.a c.b c.ha c.hb H i hH

theorem irrelevant_forward (c : Chart K) :
    HomogeneousIdeal.irrelevant (grading K) ≤
      (HomogeneousIdeal.irrelevant (originalGrading K)).map (forward c) := by
  apply (HomogeneousIdeal.irrelevant_le (grading K)).mpr
  intro i hi H hH
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem (originalGrading K) hi
    ((backward c).map_mem hH)
  have hmap := Ideal.mem_map_of_mem (forward c).toRingHom hm
  have he : (forward c) ((backward c) H) = H := c.coordinates.apply_symm_apply H
  change (forward c) ((backward c) H) ∈ _ at hmap
  rw [he] at hmap
  exact hmap

theorem irrelevant_backward (c : Chart K) :
    HomogeneousIdeal.irrelevant (originalGrading K) ≤
      (HomogeneousIdeal.irrelevant (grading K)).map (backward c) := by
  apply (HomogeneousIdeal.irrelevant_le (originalGrading K)).mpr
  intro i hi H hH
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem (grading K) hi
    ((forward c).map_mem hH)
  have hmap := Ideal.mem_map_of_mem (backward c).toRingHom hm
  have he : (backward c) ((forward c) H) = H := c.coordinates.symm_apply_apply H
  change (backward c) ((forward c) H) ∈ _ at hmap
  rw [he] at hmap
  exact hmap

theorem forward_comp_backward (c : Chart K) :
    (forward c).comp (backward c) = GradedRingHom.id (grading K) := by
  apply GradedRingHom.ext
  intro H
  exact c.coordinates.apply_symm_apply H

theorem backward_comp_forward (c : Chart K) :
    (backward c).comp (forward c) = GradedRingHom.id (originalGrading K) := by
  apply GradedRingHom.ext
  intro H
  exact c.coordinates.symm_apply_apply H

def coordinateIso (c : Chart K) : projectivePlane K ≅ originalPlane K where
  hom := Proj.map (forward c) (irrelevant_forward c)
  inv := Proj.map (backward c) (irrelevant_backward c)
  hom_inv_id := by
    have h := Proj.map_comp (backward c) (forward c) (irrelevant_backward c) (irrelevant_forward c)
    simpa only [forward_comp_backward, Proj.map_id] using h.symm
  inv_hom_id := by
    have h := Proj.map_comp (forward c) (backward c) (irrelevant_forward c) (irrelevant_backward c)
    simpa only [backward_comp_forward, Proj.map_id] using h.symm

theorem membership (c : Chart K) (q : projectivePlane K) (H : PlaneRing K) :
    H ∈ ((coordinateIso c).hom q).asHomogeneousIdeal ↔
      c.coordinates H ∈ q.asHomogeneousIdeal := Iff.rfl

def stalkEquiv (c : Chart K) (q : projectivePlane K) :
    (originalPlane K).presheaf.stalk ((coordinateIso c).hom q) ≃+*
      (projectivePlane K).presheaf.stalk q :=
  (asIso ((coordinateIso c).hom.stalkMap q)).commRingCatIsoToRingEquiv

theorem stalkEquiv_apply (c : Chart K) (q : projectivePlane K)
    (s : (originalPlane K).presheaf.stalk ((coordinateIso c).hom q)) :
    stalkEquiv c q s = (coordinateIso c).hom.stalkMap q s := rfl

end Cylinder.ProjectiveCoordinateIso
end
