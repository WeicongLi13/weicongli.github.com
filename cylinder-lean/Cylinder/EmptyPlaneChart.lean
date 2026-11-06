module

public import Cylinder.ProjectivePointSet
public import Cylinder.ProjectiveCylinderChart

/-!
# Taking an empty plane as the plane at infinity

This is Lemma `lem:infinity`. A genuine projective coordinate change
sends the given empty plane to infinity. Its affine chart preserves
cardinality, divisibility of every plane intersection, and the cylinder
property in both directions.
-/

@[expose] public section

noncomputable section

namespace Cylinder.EmptyPlaneChart

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveChart
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

theorem empty_plane_functional_nonzero {S : Finset (Geometry.Point p)} {H : DualPoint p}
    (hempty : intersection p S H = ∅) :
    ∀ x ∈ S, H.rep (affineVector p x) ≠ 0 := by
  intro x hx hzero
  have hi : Incident p (affineEmbed p x) H := by
    have h := incident_mk_mk p (affineVector p x) H.rep (affineVector_ne_zero p x) H.rep_nonzero
    have h' : Incident p (affineEmbed p x) H ↔ H.rep (affineVector p x) = 0 := by
      simpa only [affineEmbed, Projectivization.mk_rep] using h
    exact h'.mpr hzero
  have hmem : affineEmbed p x ∈ intersection p S H :=
    Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, hi⟩
  rw [hempty] at hmem
  simp at hmem

theorem pDivisible_chartImage (e : Vector p ≃ₗ[ZMod p] Vector p)
    {S : Finset (Geometry.Point p)} (havoid : AvoidsChart p e S)
    (hS : Geometry.PDivisible p S) : Geometry.PDivisible p (S.image (chartMap p e)) := by
  apply (pDivisible_iff p _).mpr
  intro H'
  obtain ⟨H, rfl⟩ := mapDual_surjective p e H'
  rw [intersection_card, planeIntersection_chartImage_card p e S havoid]
  have h := intersection_card_dvd p hS H
  rwa [intersection_card] at h

theorem pDivisible_chartImage_iff (e : Vector p ≃ₗ[ZMod p] Vector p)
    {S : Finset (Geometry.Point p)} (havoid : AvoidsChart p e S) :
    Geometry.PDivisible p (S.image (chartMap p e)) ↔ Geometry.PDivisible p S := by
  constructor
  · intro h
    have hback := pDivisible_chartImage p e.symm (chartImage_avoids_inverse p e S havoid) h
    simpa only [inverse_chartImage p e S havoid] using hback
  · exact pDivisible_chartImage p e havoid

/-- The full empty-plane recharting assertion from the manuscript. -/
theorem empty_plane_as_infinity (S : Finset (Geometry.Point p)) (H : DualPoint p)
    (hempty : intersection p S H = ∅) :
    ∃ e : Vector p ≃ₗ[ZMod p] Vector p,
      AvoidsChart p e S ∧ mapDual p e H = infinity p ∧
      (S.image (chartMap p e)).card = S.card ∧
      (Geometry.PDivisible p (S.image (chartMap p e)) ↔ Geometry.PDivisible p S) ∧
      (Geometry.IsCylinder p (S.image (chartMap p e)) ↔ Geometry.IsCylinder p S) ∧
      ∀ H' : DualPoint p,
        (intersection p (S.image (chartMap p e)) (mapDual p e H')).card =
          (intersection p S H').card := by
  obtain ⟨e, he, havoid, hinf, hcard, hcy, hplanes⟩ :=
    ProjectiveCylinderChart.exists_chart_of_empty_plane p S H.rep H.rep_nonzero
      (empty_plane_functional_nonzero p hempty)
  refine ⟨e, havoid, ?_, hcard, pDivisible_chartImage_iff p e havoid, hcy, ?_⟩
  · simpa only [Projectivization.mk_rep] using hinf
  · intro H'
    rw [intersection_card, intersection_card]
    exact hplanes H'

end Cylinder.EmptyPlaneChart

end
