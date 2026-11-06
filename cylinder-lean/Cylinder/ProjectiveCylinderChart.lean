module

public import Cylinder.ProjectiveChart

/-!
# Cylinder preservation under a change to an empty plane at infinity

An empty homogeneous plane contains the direction of every complete affine
line in the point set. Therefore normalization in the new chart maps all
the complete lines of a cylinder to complete parallel affine lines.
-/

@[expose] public section

namespace Cylinder.ProjectiveCylinderChart

open Cylinder.Geometry Cylinder.ProjectiveGeometry Cylinder.ProjectiveChart
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

def directionVector (v : Geometry.Point p) : ProjectiveGeometry.Vector p := Fin.cons 0 v

theorem directionVector_ne_zero {v : Geometry.Point p} (hv : v ≠ 0) :
    directionVector p v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i.succ
  simpa [directionVector] using this

theorem affineVector_on_line (base v : Geometry.Point p) (t : ZMod p) :
    affineVector p (base + t • v) = affineVector p base + t • directionVector p v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [directionVector]
  · simp [directionVector]

theorem functional_on_line (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p))
    (base v : Geometry.Point p) (t : ZMod p) :
    f (affineVector p (base + t • v)) =
      f (affineVector p base) + t * f (directionVector p v) := by
  rw [affineVector_on_line, map_add, map_smul]
  rfl

/-- An empty homogeneous plane contains the direction of any complete affine line it misses. -/
theorem functional_direction_zero_of_line_avoids
    (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)) (base v : Geometry.Point p)
    (h : ∀ t : ZMod p, f (affineVector p (base + t • v)) ≠ 0) :
    f (directionVector p v) = 0 := by
  by_contra hdir
  apply h (-f (affineVector p base) / f (directionVector p v))
  rw [functional_on_line, div_mul_cancel₀ _ hdir, add_neg_cancel]

theorem functional_direction_zero_of_empty_plane
    (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p))
    {S : Finset (Geometry.Point p)} (hS : ∀ x ∈ S, f (affineVector p x) ≠ 0)
    (base v : Geometry.Point p) (hline : affineLine p base v ⊆ S) :
    f (directionVector p v) = 0 := by
  apply functional_direction_zero_of_line_avoids p f base v
  intro t
  apply hS _
  apply hline
  exact (mem_affineLine p base v _).mpr ⟨t, rfl⟩

variable (g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)

def firstFunctional : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p) :=
  (LinearMap.proj (0 : Fin 4)).comp g.toLinearMap

def transformedDirection (v : Geometry.Point p) : Geometry.Point p :=
  fun i => g (directionVector p v) i.succ

theorem transformedDirection_ne_zero {v : Geometry.Point p} (hv : v ≠ 0)
    (hfirst : g (directionVector p v) 0 = 0) : transformedDirection p g v ≠ 0 := by
  intro htail
  apply directionVector_ne_zero p hv
  apply g.injective
  change g (directionVector p v) = g 0
  rw [map_zero]
  funext i
  refine Fin.cases hfirst (fun j => ?_) i
  exact congrFun htail j

theorem chartMap_on_line (base v : Geometry.Point p)
    (hfirst : g (directionVector p v) 0 = 0) (t : ZMod p) :
    chartMap p g (base + t • v) = chartMap p g base +
      (t / g (affineVector p base) 0) • transformedDirection p g v := by
  funext i
  simp [chartMap, affineVector_on_line, map_add, map_smul, hfirst,
    transformedDirection, div_eq_mul_inv]
  ring

theorem image_affineLine (base v : Geometry.Point p)
    (hfirst : g (directionVector p v) 0 = 0) (hbase : g (affineVector p base) 0 ≠ 0) :
    (affineLine p base v).image (chartMap p g) =
      affineLine p (chartMap p g base) (transformedDirection p g v) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, rfl⟩ := (mem_affineLine p base v x).mp hx
    rw [mem_affineLine]
    exact ⟨t / g (affineVector p base) 0, (chartMap_on_line p g base v hfirst t).symm⟩
  · intro hy
    obtain ⟨t, rfl⟩ := (mem_affineLine p (chartMap p g base) (transformedDirection p g v) y).mp hy
    apply Finset.mem_image.mpr
    refine ⟨base + (t * g (affineVector p base) 0) • v,
      (mem_affineLine p base v _).mpr ⟨_, rfl⟩, ?_⟩
    rw [chartMap_on_line p g base v hfirst]
    simp [hbase]

/-- A cylinder remains an actual union of `p` disjoint parallel full lines in the new chart. -/
theorem isCylinder_chartImage {S : Finset (Geometry.Point p)}
    (hS : AvoidsChart p g S) (hcy : IsCylinder p S) :
    IsCylinder p (S.image (chartMap p g)) := by
  obtain ⟨v, hv, base, hdisjoint, hUnion⟩ := hcy
  have hline : ∀ i : Fin p, affineLine p (base i) v ⊆ S := by
    intro i x hx
    rw [hUnion]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  let i0 : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  have hfirst : g (directionVector p v) 0 = 0 :=
    functional_direction_zero_of_empty_plane p (firstFunctional p g)
      hS (base i0) v (hline i0)
  have hbase : ∀ i : Fin p, g (affineVector p (base i)) 0 ≠ 0 := by
    intro i
    exact hS _ (hline i (base_mem_affineLine p (base i) v))
  refine ⟨transformedDirection p g v, transformedDirection_ne_zero p g hv hfirst,
    (fun i => chartMap p g (base i)), ?_, ?_⟩
  · intro i j hij
    rw [← image_affineLine p g (base i) v hfirst (hbase i),
      ← image_affineLine p g (base j) v hfirst (hbase j)]
    apply Finset.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨x, hxi, hxy⟩ := Finset.mem_image.mp hyi
    obtain ⟨z, hzj, hzy⟩ := Finset.mem_image.mp hyj
    have hxz := chartMap_injective p g (hS x (hline i hxi)) (hS z (hline j hzj))
      (hxy.trans hzy.symm)
    subst z
    exact Finset.disjoint_left.mp (hdisjoint hij) hxi hzj
  · rw [hUnion, Finset.biUnion_image]
    congr 1
    funext i
    exact image_affineLine p g (base i) v hfirst (hbase i)

/-- The cylinder property is equivalent in both affine charts on a set avoiding their boundary. -/
theorem isCylinder_chartImage_iff {S : Finset (Geometry.Point p)} (hS : AvoidsChart p g S) :
    IsCylinder p (S.image (chartMap p g)) ↔ IsCylinder p S := by
  constructor
  · intro hcy
    have hback := isCylinder_chartImage p g.symm (chartImage_avoids_inverse p g S hS) hcy
    simpa only [inverse_chartImage p g S hS] using hback
  · exact isCylinder_chartImage p g hS

/-- A specified empty homogeneous plane admits a genuine new affine chart preserving all counts
and preserving the cylinder property in both directions. -/
theorem exists_chart_of_empty_plane (S : Finset (Geometry.Point p))
    (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)) (hf : f ≠ 0)
    (hempty : ∀ x ∈ S, f (affineVector p x) ≠ 0) :
    ∃ e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p,
      (∀ x, e x 0 = f x) ∧ AvoidsChart p e S ∧
      mapDual p e (Projectivization.mk (ZMod p) f hf) = infinity p ∧
      (S.image (chartMap p e)).card = S.card ∧
      (IsCylinder p (S.image (chartMap p e)) ↔ IsCylinder p S) ∧
      ∀ H : DualPoint p,
        ((S.image (chartMap p e)).filter
          (fun y => Incident p (affineEmbed p y) (mapDual p e H))).card =
          (S.filter (fun x => Incident p (affineEmbed p x) H)).card := by
  obtain ⟨e, he⟩ := exists_linearEquiv_first_eq p f hf
  have havoid : AvoidsChart p e S := by
    intro x hx
    rw [he]
    exact hempty x hx
  exact ⟨e, he, havoid, mapDual_eq_infinity p e f hf he,
    chartImage_card p e S havoid, isCylinder_chartImage_iff p e havoid,
    planeIntersection_chartImage_card p e S havoid⟩

#print axioms functional_direction_zero_of_empty_plane
#print axioms image_affineLine
#print axioms isCylinder_chartImage_iff
#print axioms exists_chart_of_empty_plane

end Cylinder.ProjectiveCylinderChart
