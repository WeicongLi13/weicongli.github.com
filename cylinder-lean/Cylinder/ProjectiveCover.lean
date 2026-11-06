module

public import Cylinder.ProjectiveBalance
public meta import Lean.Elab.Tactic.Omega

/-!
# Empty planes cover the complement of the actual point set

Through an outside point the intersection total is `|S|(p+1)`, obtained
by counting actual pairs of incidences. Divisibility then forces one of
the `p²+p+1` planes through that point to be empty.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveCover

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

@[simp] theorem affineEmbed_mem_pointSet (S : Finset (Geometry.Point p)) (x : Geometry.Point p) :
    affineEmbed p x ∈ pointSet p S ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    exact affineEmbed_injective p hyx ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem incident_mk_rep_iff (x : ProjectiveGeometry.Vector p) (hx : x ≠ 0)
    (H : DualPoint p) :
    Incident p (Projectivization.mk (ZMod p) x hx) H ↔ H.rep x = 0 := by
  simpa only [Projectivization.mk_rep] using
    incident_mk_mk p x H.rep hx H.rep_nonzero

theorem incident_affine_rep_iff (x : Geometry.Point p) (H : DualPoint p) :
    Incident p (affineEmbed p x) H ↔ H.rep (affineVector p x) = 0 :=
  incident_mk_rep_iff p _ (affineVector_ne_zero p x) H

@[simp] theorem mem_whitePoints (S : Finset (Geometry.Point p)) (H : DualPoint p) :
    H ∈ whitePoints p S ↔ quotient p S H = 0 := by
  simp [whitePoints, WhiteBlackWeights.white]

theorem mem_whitePoints_iff_empty {S : Finset (Geometry.Point p)} (hS : Geometry.PDivisible p S)
    (H : DualPoint p) : H ∈ whitePoints p S ↔ intersection p S H = ∅ := by
  rw [mem_whitePoints, ← Finset.card_eq_zero]
  constructor
  · intro h
    rw [← p_mul_quotient p hS H, h, mul_zero]
  · intro h
    simp [quotient, h]

theorem mem_whitePoints_iff_no_incident {S : Finset (Geometry.Point p)}
    (hS : Geometry.PDivisible p S) (H : DualPoint p) :
    H ∈ whitePoints p S ↔ ∀ x ∈ pointSet p S, ¬ Incident p x H := by
  rw [mem_whitePoints_iff_empty p hS H]
  exact Finset.filter_eq_empty_iff

theorem infinity_mem_whitePoints (S : Finset (Geometry.Point p)) :
    infinity p ∈ whitePoints p S := by
  rw [mem_whitePoints]
  simp [quotient, intersection_infinity_eq_empty]

theorem sum_intersection_through_outside (S : Finset (Geometry.Point p)) (x : PG3 p)
    (hx : x ∉ pointSet p S) :
    (∑ H ∈ IncidenceDoubleCount.through (Incident p) x, (intersection p S H).card) =
      S.card * (p + 1) := by
  have hcount : ∀ y ∈ pointSet p S,
      (IncidenceDoubleCount.through (fun y H => Incident p x H ∧ Incident p y H) y).card = p + 1 := by
    intro y hy
    exact pair_plane_count p x y (fun hxy => hx (hxy ▸ hy))
  have h := IncidenceDoubleCount.first_moment
    (fun y H => Incident p x H ∧ Incident p y H) (pointSet p S) (p + 1) hcount
  rw [IncidenceDoubleCount.through, Finset.sum_filter]
  calc
    (∑ H : DualPoint p, if Incident p x H then (intersection p S H).card else 0) =
        ∑ H : DualPoint p,
          (IncidenceDoubleCount.intersection
            (fun y H => Incident p x H ∧ Incident p y H) (pointSet p S) H).card := by
      apply Finset.sum_congr rfl
      intro H _
      by_cases hi : Incident p x H
      · simp [hi, intersection, IncidenceDoubleCount.intersection]
      · simp [hi, IncidenceDoubleCount.intersection]
    _ = S.card * (p + 1) := by simpa only [pointSet_card] using h

/-- Every projective point outside `S` lies on an actual empty plane. -/
theorem exists_white_through_outside {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (x : PG3 p)
    (hx : x ∉ pointSet p S) :
    ∃ H ∈ whitePoints p S, Incident p x H := by
  by_contra hno
  have hlower : p * (IncidenceDoubleCount.through (Incident p) x).card ≤
      ∑ H ∈ IncidenceDoubleCount.through (Incident p) x, (intersection p S H).card := by
    calc
      p * (IncidenceDoubleCount.through (Incident p) x).card =
          ∑ _H ∈ IncidenceDoubleCount.through (Incident p) x, p := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro H hH
        have hpos : 0 < (intersection p S H).card := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hno
          refine ⟨H, (mem_whitePoints_iff_empty p hS H).mpr (Finset.card_eq_zero.mp hz), ?_⟩
          exact (Finset.mem_filter.mp hH).2
        exact Nat.le_of_dvd hpos (intersection_card_dvd p hS H)
  rw [point_plane_count, sum_intersection_through_outside p S x hx, hcard] at hlower
  have hpoly : p * (p ^ 2 + p + 1) = p ^ 2 * (p + 1) + p := by ring
  rw [hpoly] at hlower
  have hp : 0 < p := (Fact.out : p.Prime).pos
  omega

theorem mem_pointSet_iff_no_white {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (x : PG3 p) :
    x ∈ pointSet p S ↔ ∀ H ∈ whitePoints p S, ¬ Incident p x H := by
  constructor
  · intro hx H hH
    exact (mem_whitePoints_iff_no_incident p hS H).mp hH x hx
  · intro h
    by_contra hx
    obtain ⟨H, hH, hi⟩ := exists_white_through_outside p hcard hS x hx
    exact h H hH hi

def emptyPlaneUnion (S : Finset (Geometry.Point p)) : Finset (PG3 p) :=
  (whitePoints p S).biUnion (fun H => Finset.univ.filter (fun x => Incident p x H))

/-- The point set is precisely the complement of the union of its empty projective planes. -/
theorem pointSet_eq_complement {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    pointSet p S = Finset.univ \ emptyPlaneUnion p S := by
  ext x
  rw [mem_pointSet_iff_no_white p hcard hS x]
  simp [emptyPlaneUnion]

#print axioms sum_intersection_through_outside
#print axioms exists_white_through_outside
#print axioms pointSet_eq_complement

end Cylinder.ProjectiveCover

end
