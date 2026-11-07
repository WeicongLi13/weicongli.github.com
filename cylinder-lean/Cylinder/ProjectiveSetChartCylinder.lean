module

public import Cylinder.ProjectiveSetChart
public import Cylinder.ProjectiveCylinderChart

/-! A cylinder as an exact union of genuine concurrent projective lines.
The line objects are two-dimensional vector subspaces. Their pairwise
intersection is the one-dimensional subspace of the common centre. -/

@[expose] public section
noncomputable section
namespace Cylinder.ProjectiveSetChart

open Cylinder.Geometry Cylinder.ProjectiveGeometry Cylinder.ProjectiveChart
open Cylinder.ProjectiveCylinderChart
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- The intrinsic projective conclusion, with exact membership in the original set. -/
def IsProjectiveCylinder (H : DualPoint p) (S : Finset (PG3 p)) : Prop :=
  ∃ centre : PG3 p, Incident p centre H ∧
    ∃ L : Fin p → Submodule (ZMod p) (ProjectiveGeometry.Vector p),
      (∀ i, Module.finrank (ZMod p) (L i) = 2) ∧
      Pairwise (fun i j => L i ≠ L j) ∧
      (∀ i, centre ∈ (L i).projectivization) ∧
      Pairwise (fun i j => L i ⊓ L j = centre.submodule) ∧
      ∀ x : PG3 p, x ∈ S ↔ x ≠ centre ∧ ∃ i : Fin p, x ∈ (L i).projectivization

def lineSpace (base v : Geometry.Point p) :
    Submodule (ZMod p) (ProjectiveGeometry.Vector p) :=
  Submodule.span (ZMod p) {affineVector p base, directionVector p v}

def directionPoint (v : Geometry.Point p) (hv : v ≠ 0) : PG3 p :=
  Projectivization.mk (ZMod p) (directionVector p v) (directionVector_ne_zero p hv)

theorem directionPoint_incident (v : Geometry.Point p) (hv : v ≠ 0) :
    Incident p (directionPoint p v hv) (infinity p) := by
  simp [directionPoint, infinity, directionVector]

theorem affineEmbed_ne_directionPoint (a v : Geometry.Point p) (hv : v ≠ 0) :
    affineEmbed p a ≠ directionPoint p v hv := by
  intro h
  apply affineEmbed_not_incident_infinity p a
  rw [h]
  exact directionPoint_incident p v hv

theorem lineSpace_finrank (base v : Geometry.Point p) (hv : v ≠ 0) :
    Module.finrank (ZMod p) (lineSpace p base v) = 2 := by
  let f : Fin 2 → ProjectiveGeometry.Vector p := ![affineVector p base, directionVector p v]
  have hf : LinearIndependent (ZMod p) f := by
    rw [linearIndependent_fin2]
    refine ⟨directionVector_ne_zero p hv, ?_⟩
    intro a h
    have h0 := congrFun h 0
    simpa [f, directionVector] using h0
  have hr : Set.range f = {affineVector p base, directionVector p v} := by
    ext w
    simp [f, or_comm]
  have he : Submodule.span (ZMod p) (Set.range f) = lineSpace p base v := by
    rw [hr]
    rfl
  calc
    Module.finrank (ZMod p) (lineSpace p base v) =
        Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range f)) :=
      (LinearEquiv.ofEq _ _ he).finrank_eq.symm
    _ = 2 := by simpa using finrank_span_eq_card hf

theorem mem_direction_submodule (x c : PG3 p) :
    x ∈ c.submodule.projectivization ↔ x = c := by
  induction x using Projectivization.ind with
  | h w hw =>
    induction c using Projectivization.ind with
    | h d hd =>
      simp only [Projectivization.submodule_mk, Submodule.mk_mem_projectivization_iff,
        Submodule.mem_span_singleton, Projectivization.mk_eq_mk_iff']

/-- Homogenizing a full affine line adds exactly its single point at infinity. -/
theorem mem_lineSpace_iff (base v : Geometry.Point p) (hv : v ≠ 0) (x : PG3 p) :
    x ∈ (lineSpace p base v).projectivization ↔
      x = directionPoint p v hv ∨
        ∃ a ∈ affineLine p base v, affineEmbed p a = x := by
  constructor
  · induction x using Projectivization.ind with
    | h w hw =>
      intro hx
      change w ∈ Submodule.span (ZMod p) {affineVector p base, directionVector p v} at hx
      obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hx
      by_cases hs : s = 0
      · left
        unfold directionPoint
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨t, by simpa [hs] using hst⟩
      · right
        refine ⟨base + (t / s) • v, (mem_affineLine p base v _).mpr ⟨_, rfl⟩, ?_⟩
        symm
        unfold affineEmbed
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨s, ?_⟩
        rw [affineVector_on_line, smul_add, smul_smul]
        have hcoef : s * (t / s) = t := by rw [mul_comm, div_mul_cancel₀ _ hs]
        rw [hcoef]
        exact hst
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · change directionVector p v ∈ lineSpace p base v
      exact Submodule.subset_span (by simp)
    · obtain ⟨t, rfl⟩ := (mem_affineLine p base v a).mp ha
      change affineVector p (base + t • v) ∈ lineSpace p base v
      rw [affineVector_on_line]
      apply Submodule.add_mem
      · exact Submodule.subset_span (by simp)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem lineSpace_inf (a b v : Geometry.Point p) (hv : v ≠ 0)
    (hdis : Disjoint (affineLine p a v) (affineLine p b v)) :
    lineSpace p a v ⊓ lineSpace p b v = (directionPoint p v hv).submodule := by
  apply Submodule.ext
  intro w
  by_cases hw : w = 0
  · simp [hw]
  let x : PG3 p := Projectivization.mk (ZMod p) w hw
  have hmem (U : Submodule (ZMod p) (ProjectiveGeometry.Vector p)) :
      w ∈ U ↔ x ∈ U.projectivization := Iff.rfl
  rw [Submodule.mem_inf, hmem, hmem, hmem, mem_direction_submodule,
    mem_lineSpace_iff p a v hv, mem_lineSpace_iff p b v hv]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with hc | ⟨y, hy, hxy⟩
    · exact hc
    rcases h2 with hc | ⟨z, hz, hxz⟩
    · exact hc
    have hyz := affineEmbed_injective p (hxy.trans hxz.symm)
    subst z
    exact False.elim (Finset.disjoint_left.mp hdis hy hz)
  · intro hc
    exact ⟨Or.inl hc, Or.inl hc⟩

theorem lineSpace_ne (a b v : Geometry.Point p) (hv : v ≠ 0)
    (hdis : Disjoint (affineLine p a v) (affineLine p b v)) :
    lineSpace p a v ≠ lineSpace p b v := by
  intro he
  have ha : affineEmbed p a ∈ (lineSpace p a v).projectivization :=
    (mem_lineSpace_iff p a v hv _).mpr
      (Or.inr ⟨a, base_mem_affineLine p a v, rfl⟩)
  rw [he] at ha
  rcases (mem_lineSpace_iff p b v hv _).mp ha with hc | ⟨z, hz, hza⟩
  · exact affineEmbed_ne_directionPoint p a v hv hc
  · have hz' := affineEmbed_injective p hza
    subst z
    exact Finset.disjoint_left.mp hdis (base_mem_affineLine p a v) hz

/-- The affine cylinder supplies actual distinct concurrent projective lines. -/
theorem isProjectiveCylinder_affineImage (T : Finset (Geometry.Point p))
    (hT : IsCylinder p T) :
    IsProjectiveCylinder p (infinity p) (T.image (affineEmbed p)) := by
  obtain ⟨v, hv, base, hd, hu⟩ := hT
  refine ⟨directionPoint p v hv, directionPoint_incident p v hv,
    (fun i => lineSpace p (base i) v), (fun i => lineSpace_finrank p (base i) v hv),
    (fun i j hij => lineSpace_ne p (base i) (base j) v hv (hd hij)),
    (fun i => (mem_lineSpace_iff p (base i) v hv _).mpr (Or.inl rfl)),
    (fun i j hij => lineSpace_inf p (base i) (base j) v hv (hd hij)), ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [hu] at ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    exact ⟨affineEmbed_ne_directionPoint p a v hv,
      i, (mem_lineSpace_iff p (base i) v hv _).mpr (Or.inr ⟨a, hi, rfl⟩)⟩
  · rintro ⟨hne, i, hi⟩
    rcases (mem_lineSpace_iff p (base i) v hv x).mp hi with hc | ⟨a, ha, rfl⟩
    · exact False.elim (hne hc)
    · apply Finset.mem_image.mpr
      refine ⟨a, ?_, rfl⟩
      rw [hu]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩

variable (g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)

theorem mapPoint_mem_map (x : PG3 p)
    (U : Submodule (ZMod p) (ProjectiveGeometry.Vector p)) :
    mapPoint p g x ∈ (U.map g.toLinearMap).projectivization ↔ x ∈ U.projectivization := by
  induction x using Projectivization.ind with
  | h w hw => simp [mapPoint, Projectivization.map_mk]

theorem mapPoint_submodule (x : PG3 p) :
    (mapPoint p g x).submodule = x.submodule.map g.toLinearMap := by
  induction x using Projectivization.ind with
  | h w hw =>
    simp [mapPoint, Projectivization.map_mk, Projectivization.submodule_mk, Submodule.map_span]

/-- The intrinsic geometric predicate is transported by an actual projective collineation. -/
theorem isProjectiveCylinder_map (H : DualPoint p) (S : Finset (PG3 p))
    (hS : IsProjectiveCylinder p H S) :
    IsProjectiveCylinder p (mapDual p g H) (S.image (mapPoint p g)) := by
  obtain ⟨c, hc, L, hdim, hne, hcentre, hinf, hmem⟩ := hS
  refine ⟨mapPoint p g c, (incident_mapPoint_mapDual p g c H).mpr hc,
    (fun i => (L i).map g.toLinearMap), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [LinearEquiv.finrank_map_eq, hdim]
  · intro i j hij he
    apply hne hij
    exact Submodule.map_injective_of_injective g.injective he
  · intro i
    exact (mapPoint_mem_map p g c (L i)).mpr (hcentre i)
  · intro i j hij
    rw [← Submodule.map_inf _ g.injective, hinf hij, mapPoint_submodule]
  · intro x
    have hpre : mapPoint p g (mapPoint p g.symm x) = x := by
      simpa using mapPoint_inverse p g.symm x
    have himage : mapPoint p g (mapPoint p g.symm x) ∈ S.image (mapPoint p g) ↔
        mapPoint p g.symm x ∈ S := by
      constructor
      · intro hx
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
        have he' := mapPoint_injective p g he
        exact he' ▸ hy
      · intro hx
        exact Finset.mem_image.mpr ⟨_, hx, rfl⟩
    rw [← hpre, himage, hmem]
    simp only [mapPoint_mem_map]
    constructor
    · rintro ⟨hne', hi⟩
      exact ⟨fun he => hne' (mapPoint_injective p g he), hi⟩
    · rintro ⟨hne', hi⟩
      exact ⟨fun he => hne' (congrArg (mapPoint p g) he), hi⟩

/-- Reconstructing the chart cylinder gives the requested geometry on the original set. -/
theorem isProjectiveCylinder_of_chart (H : DualPoint p)
    (hH : mapDual p g H = infinity p) (S : Finset (PG3 p))
    (havoid : ∀ x ∈ S, ¬ Incident p x H)
    (hcy : IsCylinder p (chartSet p g S)) : IsProjectiveCylinder p H S := by
  have h := isProjectiveCylinder_map p g.symm (infinity p)
    ((chartSet p g S).image (affineEmbed p))
    (isProjectiveCylinder_affineImage p (chartSet p g S) hcy)
  have hh : mapDual p g.symm (infinity p) = H := by rw [← hH, mapDual_inverse]
  rw [hh, Finset.image_image] at h
  change IsProjectiveCylinder p H ((chartSet p g S).image (inverseEmbed p g)) at h
  rw [inverseEmbed_chartSet p g H hH S havoid] at h
  exact h

#print axioms lineSpace_finrank
#print axioms mem_lineSpace_iff
#print axioms lineSpace_inf
#print axioms isProjectiveCylinder_affineImage
#print axioms isProjectiveCylinder_map
#print axioms isProjectiveCylinder_of_chart

end Cylinder.ProjectiveSetChart
