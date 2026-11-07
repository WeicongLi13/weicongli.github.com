module

public import Cylinder.ProjectiveChart
public import Cylinder.ProjectivePointSet

/-! An affine chart for an arbitrary finite set of actual projective points.
No assumption that the original set was already an affine image is used. -/

@[expose] public section
noncomputable section
namespace Cylinder.ProjectiveSetChart

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveChart
open scoped Classical

variable (p : ℕ) [Fact p.Prime]
variable (g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)

theorem mapPoint_inverse (x : PG3 p) : mapPoint p g.symm (mapPoint p g x) = x := by
  induction x using Projectivization.ind with
  | h v hv => simp [mapPoint, Projectivization.map_mk]

/-- The inverse affine chart takes points directly into the original projective space. -/
def inverseEmbed (x : Geometry.Point p) : PG3 p := mapPoint p g.symm (affineEmbed p x)

theorem inverseEmbed_injective : Function.Injective (inverseEmbed p g) :=
  (mapPoint_injective p g.symm).comp (affineEmbed_injective p)

theorem exists_affineEmbed_of_not_infinity (x : PG3 p)
    (hx : ¬ Incident p x (infinity p)) : ∃ a, affineEmbed p a = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    have hv0 : v 0 ≠ 0 := by simpa [infinity] using hx
    let a : Geometry.Point p := fun i => v i.succ / v 0
    refine ⟨a, ?_⟩
    unfold affineEmbed
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(v 0)⁻¹, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hv0]
    · simp [a, div_eq_mul_inv, mul_comm]

theorem exists_inverseEmbed (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (x : PG3 p)
    (hx : ¬ Incident p x H) : ∃ a, inverseEmbed p g a = x := by
  have hn : ¬ Incident p (mapPoint p g x) (infinity p) := by
    rw [← hH, incident_mapPoint_mapDual]
    exact hx
  obtain ⟨a, ha⟩ := exists_affineEmbed_of_not_infinity p (mapPoint p g x) hn
  refine ⟨a, ?_⟩
  unfold inverseEmbed
  rw [ha, mapPoint_inverse]

/-- Pull back any finite projective set to the chosen affine chart. -/
def chartSet (S : Finset (PG3 p)) : Finset (Geometry.Point p) :=
  Finset.univ.filter (fun a => inverseEmbed p g a ∈ S)

@[simp] theorem mem_chartSet (S : Finset (PG3 p)) (a : Geometry.Point p) :
    a ∈ chartSet p g S ↔ inverseEmbed p g a ∈ S := by simp [chartSet]

/-- Exact reconstruction of the original arbitrary projective point set. -/
theorem inverseEmbed_chartSet (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H) :
    (chartSet p g S).image (inverseEmbed p g) = S := by
  ext x
  constructor
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_chartSet p g S a).mp ha
  · intro hx
    obtain ⟨a, rfl⟩ := exists_inverseEmbed p g H hH x (havoid x hx)
    exact Finset.mem_image.mpr ⟨a, (mem_chartSet p g S a).mpr hx, rfl⟩

theorem chartSet_card (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H) :
    (chartSet p g S).card = S.card := by
  calc
    (chartSet p g S).card = ((chartSet p g S).image (inverseEmbed p g)).card :=
      (Finset.card_image_of_injective _ (inverseEmbed_injective p g)).symm
    _ = S.card := congrArg Finset.card (inverseEmbed_chartSet p g H hH S havoid)

theorem inverseEmbed_incident (a : Geometry.Point p) (K : DualPoint p) :
    Incident p (inverseEmbed p g a) K ↔ Incident p (affineEmbed p a) (mapDual p g K) := by
  have h := incident_mapPoint_mapDual p g (inverseEmbed p g a) K
  have hi : mapPoint p g (inverseEmbed p g a) = affineEmbed p a := by
    simpa [inverseEmbed] using mapPoint_inverse p g.symm (affineEmbed p a)
  rw [hi] at h
  exact h.symm

/-- All genuine projective-plane intersection counts are preserved. -/
theorem chartSet_intersection_card (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H) (K : DualPoint p) :
    ((chartSet p g S).filter
      (fun a => Incident p (affineEmbed p a) (mapDual p g K))).card =
      (S.filter (fun x => Incident p x K)).card := by
  have he : S.filter (fun x => Incident p x K) =
      ((chartSet p g S).filter
        (fun a => Incident p (affineEmbed p a) (mapDual p g K))).image (inverseEmbed p g) := by
    conv_lhs => rw [← inverseEmbed_chartSet p g H hH S havoid]
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact inverseEmbed_incident p g a K
  rw [he, Finset.card_image_of_injective _ (inverseEmbed_injective p g)]

theorem chartSet_pDivisible (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H)
    (hplanes : ∀ K : DualPoint p, p ∣ (S.filter (fun x => Incident p x K)).card) :
    Geometry.PDivisible p (chartSet p g S) := by
  intro a ha b
  obtain ⟨K, hK⟩ := mapDual_surjective p g (affinePlaneDual p a b ha)
  have hc := chartSet_intersection_card p g H hH S havoid K
  rw [hK] at hc
  simp only [affineEmbed_incident_affinePlaneDual] at hc
  rw [hc]
  exact hplanes K

/-- Every prescribed empty projective plane provides such a chart. -/
theorem exists_chart (H : DualPoint p) :
    ∃ g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p,
      mapDual p g H = infinity p := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_first_eq p H.rep H.rep_nonzero
  refine ⟨g, ?_⟩
  simpa only [Projectivization.mk_rep] using
    mapDual_eq_infinity p g H.rep H.rep_nonzero hg

#print axioms inverseEmbed_chartSet
#print axioms chartSet_card
#print axioms chartSet_intersection_card
#print axioms chartSet_pDivisible
#print axioms exists_chart

end Cylinder.ProjectiveSetChart
