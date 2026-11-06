module

public import Cylinder.ProjectiveGeometry
public import Cylinder.IncidenceDoubleCount
public meta import Lean.Elab.Tactic.Omega

/-!
# The actual affine point set inside projective space

Projective plane intersections are filters of the injected original
point set. Their divisibility is proved equivalent to the original
affine-plane condition, including the plane at infinity.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectivePointSet

open Cylinder.ProjectiveGeometry
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def pointSet (S : Finset (Geometry.Point p)) : Finset (PG3 p) := S.image (affineEmbed p)

def intersection (S : Finset (Geometry.Point p)) (H : DualPoint p) : Finset (PG3 p) :=
  IncidenceDoubleCount.intersection (Incident p) (pointSet p S) H

def normal (H : DualPoint p) : Geometry.Point p :=
  fun i => H.rep (Pi.single i.succ 1)

def constantTerm (H : DualPoint p) : ZMod p := H.rep (Pi.single (0 : Fin 4) 1)

theorem functional_affine_expansion (H : DualPoint p) (x : Geometry.Point p) :
    H.rep (affineVector p x) = constantTerm p H + Geometry.pairing p (normal p H) x := by
  rw [functional_expansion]
  simp [pairing, Fin.sum_univ_succ, affineVector, constantTerm, normal, Geometry.pairing]

theorem incident_affine_iff (H : DualPoint p) (x : Geometry.Point p) :
    Incident p (affineEmbed p x) H ↔
      Geometry.pairing p (normal p H) x = -constantTerm p H := by
  have h : Incident p (affineEmbed p x) H ↔ H.rep (affineVector p x) = 0 := by
    simpa only [affineEmbed, Projectivization.mk_rep] using
      incident_mk_mk p (affineVector p x) H.rep (affineVector_ne_zero p x) H.rep_nonzero
  rw [functional_affine_expansion] at h
  exact h.trans (by rw [add_comm, add_eq_zero_iff_eq_neg])

theorem constantTerm_ne_zero_of_normal_eq_zero {H : DualPoint p} (hn : normal p H = 0) :
    constantTerm p H ≠ 0 := by
  intro hc
  have hall : ∀ i : Fin 4, H.rep (Pi.single i 1) = 0 := by
    intro i
    refine Fin.cases hc (fun j => ?_) i
    exact congrFun hn j
  apply H.rep_nonzero
  apply LinearMap.ext
  intro v
  simpa [pairing, hall] using functional_expansion p H.rep v

theorem intersection_card (S : Finset (Geometry.Point p)) (H : DualPoint p) :
    (intersection p S H).card = (S.filter (fun x => Incident p (affineEmbed p x) H)).card := by
  unfold intersection IncidenceDoubleCount.intersection pointSet
  rw [Finset.filter_image, Finset.card_image_of_injective _ (affineEmbed_injective p)]

@[simp] theorem pointSet_card (S : Finset (Geometry.Point p)) :
    (pointSet p S).card = S.card := Finset.card_image_of_injective _ (affineEmbed_injective p)

theorem intersection_infinity_eq_empty (S : Finset (Geometry.Point p)) :
    intersection p S (infinity p) = ∅ := by
  unfold intersection IncidenceDoubleCount.intersection pointSet
  apply Finset.filter_eq_empty_iff.mpr
  intro x hx hi
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact affineEmbed_not_incident_infinity p y hi

theorem intersection_card_dvd {S : Finset (Geometry.Point p)}
    (hS : Geometry.PDivisible p S) (H : DualPoint p) : p ∣ (intersection p S H).card := by
  rw [intersection_card]
  by_cases hn : normal p H = 0
  · have hc := constantTerm_ne_zero_of_normal_eq_zero p hn
    have hempty : S.filter (fun x => Incident p (affineEmbed p x) H) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hx
      rw [incident_affine_iff, hn, Geometry.pairing] at hx
      have hzero : constantTerm p H = 0 := by simpa using hx
      exact hc hzero
    rw [hempty, Finset.card_empty]
    exact dvd_zero p
  · have heq : S.filter (fun x => Incident p (affineEmbed p x) H) =
        S.filter (fun x => Geometry.pairing p (normal p H) x = -constantTerm p H) := by
      ext x
      simp only [Finset.mem_filter, incident_affine_iff]
    rw [heq]
    exact hS (normal p H) hn (-constantTerm p H)

/-- Divisibility in the projective model is exactly the original
divisibility condition, rather than a new assumption. -/
theorem pDivisible_iff (S : Finset (Geometry.Point p)) :
    Geometry.PDivisible p S ↔ ∀ H : DualPoint p, p ∣ (intersection p S H).card := by
  constructor
  · exact intersection_card_dvd p
  · intro h a ha b
    have hh := h (affinePlaneDual p a b ha)
    rw [intersection_card] at hh
    simpa only [affineEmbed_incident_affinePlaneDual] using hh

end Cylinder.ProjectivePointSet

end
