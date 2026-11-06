module

public import Cylinder.ProjectiveGeometry

/-!
# Changing the affine chart of actual projective space

A nonzero homogeneous plane functional is realized as the first coordinate
of an invertible linear map. Division by that first coordinate gives an
actual affine chart on its complement.
-/

@[expose] public section

namespace Cylinder.ProjectiveChart

open Cylinder.ProjectiveGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical

variable (p : ℕ) [Fact p.Prime]

theorem exists_linearEquiv_single_to {a : ProjectiveGeometry.Vector p} (ha : a ≠ 0) :
    ∃ e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p,
      e (Pi.single (0 : Fin 4) 1) = a := by
  classical
  let u : Fin 1 → ProjectiveGeometry.Vector p := fun _ => Pi.single (0 : Fin 4) 1
  let w : Fin 1 → ProjectiveGeometry.Vector p := fun _ => a
  have hu : LinearIndependent (ZMod p) u := linearIndependent_unique_iff.mpr (by
    intro h
    have := congrFun h 0
    simpa [u] using this)
  have hw : LinearIndependent (ZMod p) w := linearIndependent_unique_iff.mpr ha
  let f : Submodule.span (ZMod p) (Set.range u) ≃ₗ[ZMod p]
      Submodule.span (ZMod p) (Set.range w) :=
    hu.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  let : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) (Set.range u)) :=
    FiniteDimensional.span_of_finite (ZMod p) (Set.finite_range u)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, ?_⟩
  simpa [f, u, w] using (he (hu.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1))).symm

/-- Every nonzero plane functional becomes a coordinate under an actual element of GL(4). -/
theorem exists_linearEquiv_first_eq (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p))
    (hf : f ≠ 0) :
    ∃ g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p,
      ∀ x, g x 0 = f x := by
  let a := (pairingEquiv p).symm f
  have ha : a ≠ 0 := by
    intro h
    apply hf
    calc
      f = (pairingEquiv p) a := ((pairingEquiv p).apply_symm_apply f).symm
      _ = 0 := by rw [h, map_zero]
  obtain ⟨e, he⟩ := exists_linearEquiv_single_to p ha
  let g := (pairingEquiv p).trans (e.dualMap.trans (pairingEquiv p).symm)
  refine ⟨g, fun x => ?_⟩
  calc
    g x 0 = pairingMap p (g x) (Pi.single (0 : Fin 4) 1) := by
      simp [pairingMap, pairing, Pi.single_apply]
    _ = pairingMap p x (e (Pi.single (0 : Fin 4) 1)) := by
      change (pairingEquiv p (g x)) _ = (pairingEquiv p x) _
      simp [g]
    _ = pairingMap p x a := by rw [he]
    _ = f x := by
      change pairing p x a = f x
      rw [pairing_comm]
      change (pairingEquiv p a) x = f x
      simp [a]

variable (g : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)

/-- Coordinates in the new affine chart, normalized by the first coordinate. -/
def chartMap (x : Geometry.Point p) : Geometry.Point p :=
  fun i => g (affineVector p x) i.succ / g (affineVector p x) 0

def AvoidsChart (S : Finset (Geometry.Point p)) : Prop :=
  ∀ x ∈ S, g (affineVector p x) 0 ≠ 0

theorem affineVector_chartMap (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0) :
    affineVector p (chartMap p g x) = (g (affineVector p x) 0)⁻¹ • g (affineVector p x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hx]
  · simp [chartMap, div_eq_mul_inv, mul_comm]

def mapPoint (x : PG3 p) : PG3 p := Projectivization.map g.toLinearMap g.injective x

theorem mapPoint_injective : Function.Injective (mapPoint p g) :=
  Projectivization.map_injective g.toLinearMap g.injective

theorem affineEmbed_chartMap (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0) :
    affineEmbed p (chartMap p g x) = mapPoint p g (affineEmbed p x) := by
  unfold affineEmbed mapPoint
  rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨(g (affineVector p x) 0)⁻¹, (affineVector_chartMap p g x hx).symm⟩

theorem chartMap_injective {x y : Geometry.Point p}
    (hx : g (affineVector p x) 0 ≠ 0) (hy : g (affineVector p y) 0 ≠ 0)
    (h : chartMap p g x = chartMap p g y) : x = y := by
  apply affineEmbed_injective p
  apply mapPoint_injective p g
  rw [← affineEmbed_chartMap p g x hx, ← affineEmbed_chartMap p g y hy, h]

theorem chartImage_card (S : Finset (Geometry.Point p)) (hS : AvoidsChart p g S) :
    (S.image (chartMap p g)).card = S.card :=
  Finset.card_image_of_injOn (fun x hx y hy h => chartMap_injective p g (hS x hx) (hS y hy) h)

theorem inverse_vector_chartMap (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0) :
    g.symm (affineVector p (chartMap p g x)) =
      (g (affineVector p x) 0)⁻¹ • affineVector p x := by
  rw [affineVector_chartMap p g x hx, map_smul, g.symm_apply_apply]

theorem inverse_chart_nonzero (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0) :
    g.symm (affineVector p (chartMap p g x)) 0 ≠ 0 := by
  rw [inverse_vector_chartMap p g x hx]
  simpa using inv_ne_zero hx

theorem chartMap_inverse (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0) :
    chartMap p g.symm (chartMap p g x) = x := by
  funext i
  change g.symm (affineVector p (chartMap p g x)) i.succ /
    g.symm (affineVector p (chartMap p g x)) 0 = x i
  rw [inverse_vector_chartMap p g x hx]
  simp [div_eq_mul_inv, hx, mul_assoc, mul_comm, mul_left_comm]

theorem chartImage_avoids_inverse (S : Finset (Geometry.Point p)) (hS : AvoidsChart p g S) :
    AvoidsChart p g.symm (S.image (chartMap p g)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact inverse_chart_nonzero p g x (hS x hx)

theorem inverse_chartImage (S : Finset (Geometry.Point p)) (hS : AvoidsChart p g S) :
    (S.image (chartMap p g)).image (chartMap p g.symm) = S := by
  rw [Finset.image_image]
  calc
    S.image (chartMap p g.symm ∘ chartMap p g) = S.image id := by
      apply Finset.image_congr
      intro x hx
      exact chartMap_inverse p g x (hS x hx)
    _ = S := Finset.image_id

/-- The contragredient action transports actual dual plane equations. -/
def mapDual (H : DualPoint p) : DualPoint p :=
  Projectivization.map g.symm.dualMap.toLinearMap g.symm.dualMap.injective H

theorem mapDual_injective : Function.Injective (mapDual p g) :=
  Projectivization.map_injective g.symm.dualMap.toLinearMap g.symm.dualMap.injective

theorem mapDual_inverse (H : DualPoint p) : mapDual p g.symm (mapDual p g H) = H := by
  induction H using Projectivization.ind with
  | h f hf =>
    simp only [mapDual, Projectivization.map_mk]
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    apply LinearMap.ext
    intro x
    simp

theorem mapDual_surjective : Function.Surjective (mapDual p g) := by
  intro H
  refine ⟨mapDual p g.symm H, ?_⟩
  simpa only [LinearEquiv.symm_symm] using mapDual_inverse p g.symm H

/-- The chosen empty plane is exactly the standard plane at infinity after transport. -/
theorem mapDual_eq_infinity (f : Module.Dual (ZMod p) (ProjectiveGeometry.Vector p))
    (hf : f ≠ 0) (hfirst : ∀ x, g x 0 = f x) :
    mapDual p g (Projectivization.mk (ZMod p) f hf) = infinity p := by
  simp only [mapDual, Projectivization.map_mk, infinity]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  simp only [one_smul]
  apply LinearMap.ext
  intro x
  change x 0 = f (g.symm x)
  simpa using hfirst (g.symm x)

theorem incident_mapPoint_mapDual (x : PG3 p) (H : DualPoint p) :
    Incident p (mapPoint p g x) (mapDual p g H) ↔ Incident p x H := by
  induction x using Projectivization.ind with
  | h x hx =>
    induction H using Projectivization.ind with
    | h f hf =>
      simp [mapPoint, mapDual, Projectivization.map_mk]

theorem incident_chartMap_mapDual (x : Geometry.Point p) (hx : g (affineVector p x) 0 ≠ 0)
    (H : DualPoint p) :
    Incident p (affineEmbed p (chartMap p g x)) (mapDual p g H) ↔
      Incident p (affineEmbed p x) H := by
  rw [affineEmbed_chartMap p g x hx, incident_mapPoint_mapDual]

theorem filter_chartImage (S : Finset (Geometry.Point p)) (hS : AvoidsChart p g S)
    (H : DualPoint p) :
    (S.image (chartMap p g)).filter (fun y => Incident p (affineEmbed p y) (mapDual p g H)) =
      (S.filter (fun x => Incident p (affineEmbed p x) H)).image (chartMap p g) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyS, hyH⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyS
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hxy⟩
    rw [← hxy] at hyH
    exact (incident_chartMap_mapDual p g x (hS x hx) H).mp hyH
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxH⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxS, hxy⟩, ?_⟩
    rw [← hxy]
    exact (incident_chartMap_mapDual p g x (hS x hxS) H).mpr hxH

/-- Every projective plane intersection count is retained in the new affine chart. -/
theorem planeIntersection_chartImage_card (S : Finset (Geometry.Point p))
    (hS : AvoidsChart p g S) (H : DualPoint p) :
    ((S.image (chartMap p g)).filter
      (fun y => Incident p (affineEmbed p y) (mapDual p g H))).card =
      (S.filter (fun x => Incident p (affineEmbed p x) H)).card := by
  classical
  rw [filter_chartImage p g S hS H]
  exact chartImage_card p g _ (fun x hx => hS x (Finset.mem_filter.mp hx).1)

#print axioms exists_linearEquiv_first_eq
#print axioms chartImage_card
#print axioms chartMap_inverse
#print axioms incident_chartMap_mapDual
#print axioms mapDual_surjective
#print axioms mapDual_eq_infinity
#print axioms planeIntersection_chartImage_card

end Cylinder.ProjectiveChart
