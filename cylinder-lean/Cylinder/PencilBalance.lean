module

public import Cylinder.DualPencils
public import Cylinder.ProjectivePointSet
public import Mathlib.Data.Fintype.BigOperators

/-!
# Intersection sums along a genuine dual pencil

The parallel affine planes partition the original finite point set.
Their dual points, together with infinity, form the actual projective
line defined in `DualPencils`.
-/

@[expose] public section

noncomputable section

namespace Cylinder.PencilBalance

open Cylinder.ProjectiveGeometry Cylinder.DualPencils
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def affineSection (S : Finset (Geometry.Point p)) (n : Geometry.Point p) (c : ZMod p) :
    Finset (Geometry.Point p) := S.filter (fun x => Geometry.pairing p n x = c)

theorem sections_pairwise_disjoint (S : Finset (Geometry.Point p)) (n : Geometry.Point p) :
    Pairwise (fun b c => Disjoint (affineSection p S n b) (affineSection p S n c)) := by
  intro b c hbc
  apply Finset.disjoint_left.mpr
  intro x hxb hxc
  have hb : Geometry.pairing p n x = b := (Finset.mem_filter.mp hxb).2
  have hc : Geometry.pairing p n x = c := (Finset.mem_filter.mp hxc).2
  exact hbc (hb.symm.trans hc)

theorem sections_union (S : Finset (Geometry.Point p)) (n : Geometry.Point p) :
    Finset.univ.biUnion (affineSection p S n) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, _hc, hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hx).1
  · intro hx
    apply Finset.mem_biUnion.mpr
    exact ⟨Geometry.pairing p n x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

theorem sum_section_card (S : Finset (Geometry.Point p)) (n : Geometry.Point p) :
    (∑ c : ZMod p, (affineSection p S n c).card) = S.card := by
  have hfilter : S.filter (fun x => Geometry.pairing p n x ∈
      (Finset.univ : Finset (ZMod p))) = S := by
    apply Finset.filter_eq_self.mpr
    intro x _hx
    exact Finset.mem_univ _
  calc
    (∑ c : ZMod p, (affineSection p S n c).card) =
        (S.filter (fun x => Geometry.pairing p n x ∈
          (Finset.univ : Finset (ZMod p)))).card :=
      Finset.sum_card_fiberwise_eq_card_filter S Finset.univ (Geometry.pairing p n)
    _ = S.card := congrArg Finset.card hfilter

theorem intersection_card_affinePlaneDual (S : Finset (Geometry.Point p))
    {n : Geometry.Point p} (hn : n ≠ 0) (c : ZMod p) :
    (ProjectivePointSet.intersection p S (affinePlaneDual p n c hn)).card =
      (affineSection p S n c).card := by
  rw [ProjectivePointSet.intersection_card]
  unfold affineSection
  congr 1
  ext x
  simp only [Finset.mem_filter, affineEmbed_incident_affinePlaneDual]

theorem sum_parameter_intersection (S : Finset (Geometry.Point p))
    {n : Geometry.Point p} (hn : n ≠ 0) :
    (∑ c : Option (ZMod p),
      (ProjectivePointSet.intersection p S (parameterDual p n hn c)).card) = S.card := by
  rw [Fintype.sum_option]
  simp only [parameterDual, ProjectivePointSet.intersection_infinity_eq_empty,
    Finset.card_empty, zero_add, intersection_card_affinePlaneDual]
  exact sum_section_card p S n

/-- The full projective line has intersection sum `|S|`, including its infinity point. -/
theorem sum_pencil_intersection (S : Finset (Geometry.Point p))
    {n : Geometry.Point p} (hn : n ≠ 0) (b : ZMod p) :
    (∑ H : PencilPoint p n b, (ProjectivePointSet.intersection p S H.val).card) = S.card := by
  calc
    (∑ H : PencilPoint p n b, (ProjectivePointSet.intersection p S H.val).card) =
        ∑ c : Option (ZMod p),
          (ProjectivePointSet.intersection p S (parameterDual p n hn c)).card := by
      exact (Fintype.sum_equiv (pencilEquiv p hn b)
        (fun c => (ProjectivePointSet.intersection p S (parameterDual p n hn c)).card)
        (fun H => (ProjectivePointSet.intersection p S H.val).card) (fun _ => rfl)).symm
    _ = S.card := sum_parameter_intersection p S hn

end Cylinder.PencilBalance

end
