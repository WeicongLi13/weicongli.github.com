module

public import Cylinder.LinearTransport

/-!
# Keeping the direction in the cylinder conclusion

The direction is part of the conclusion, rather than hidden by an
existential quantifier.  The coordinate fibre construction gives the third
direction explicitly.  Linear transport then gives the corresponding
statement in any specified nonzero direction.
-/

@[expose] public section

namespace Cylinder.Geometry

variable (p : ℕ) [Fact p.Prime]

/-- An exact union of `p` pairwise disjoint lines in the specified direction. -/
def IsCylinderInDirection (S : Finset (Point p)) (direction : Point p) : Prop :=
  direction ≠ 0 ∧ ∃ base : Fin p → Point p,
    Pairwise (fun i j => Disjoint (affineLine p (base i) direction)
      (affineLine p (base j) direction)) ∧
    S = Finset.univ.biUnion (fun i => affineLine p (base i) direction)

theorem isCylinder_of_inDirection {S : Finset (Point p)} {direction : Point p}
    (h : IsCylinderInDirection p S direction) : IsCylinder p S := ⟨direction, h⟩

theorem isCylinder_iff_exists_direction (S : Finset (Point p)) :
    IsCylinder p S ↔ ∃ direction : Point p, IsCylinderInDirection p S direction := Iff.rfl

end Cylinder.Geometry

namespace Cylinder.DirectionCylinder

open Cylinder.Geometry
open Cylinder.CoordinateProjection

variable (p : ℕ) [Fact p.Prime]

theorem fullFibre_eq_affineLine_at (base : Point p) :
    fullFibre p (project p base) = affineLine p base (verticalDirection p) := by
  ext x
  rw [mem_fullFibre, mem_affineLine]
  constructor
  · intro hproject
    refine ⟨x 2 - base 2, ?_⟩
    funext i
    fin_cases i
    · simpa [project, verticalDirection] using (congrFun hproject 0).symm
    · simpa [project, verticalDirection] using (congrFun hproject 1).symm
    · change base 2 + (x 2 - base 2) * 1 = x 2
      rw [mul_one, add_comm, sub_add_cancel]
  · rintro ⟨t, ht⟩
    rw [← ht]
    funext i
    fin_cases i <;> simp [project, verticalDirection]

theorem fibre_eq_full_of_subset {S : Finset (Point p)} {q : QuotientPoint p}
    (hfull : fullFibre p q ⊆ S) : fibre p S q = fullFibre p q := by
  apply Finset.Subset.antisymm (fibre_subset_fullFibre p S q)
  intro x hx
  exact (mem_fibre p S q x).mpr ⟨hfull hx, (mem_fullFibre p q x).mp hx⟩

/-- A line sent to the third direction becomes a full coordinate fibre of the image set. -/
theorem fullFibre_image_subset_of_affineLine_subset (g : Point p ≃ₗ[ZMod p] Point p)
    {S : Finset (Point p)} {base direction : Point p}
    (hgv : g direction = verticalDirection p) (hline : affineLine p base direction ⊆ S) :
    fullFibre p (project p (g base)) ⊆ S.image g := by
  rw [fullFibre_eq_affineLine_at, ← hgv, ← LinearTransport.image_affineLine]
  exact Finset.image_subset_image hline

theorem fibreSize_image_eq_p_of_affineLine_subset (g : Point p ≃ₗ[ZMod p] Point p)
    {S : Finset (Point p)} {base direction : Point p}
    (hgv : g direction = verticalDirection p) (hline : affineLine p base direction ⊆ S) :
    fibreSize p (S.image g) (project p (g base)) = p := by
  rw [fibreSize, fibre_eq_full_of_subset p
    (fullFibre_image_subset_of_affineLine_subset p g hgv hline), fullFibre_card]

theorem inDirection_image (g : Point p ≃ₗ[ZMod p] Point p) {S : Finset (Point p)}
    {direction : Point p} (hS : IsCylinderInDirection p S direction) :
    IsCylinderInDirection p (S.image g) (g direction) := by
  obtain ⟨hd, base, hdisjoint, hUnion⟩ := hS
  have hgd : g direction ≠ 0 := by
    intro hzero
    apply hd
    exact g.injective (by simpa using hzero)
  refine ⟨hgd, (fun i => g (base i)), ?_, ?_⟩
  · intro i j hij
    rw [← LinearTransport.image_affineLine p g (base i) direction,
      ← LinearTransport.image_affineLine p g (base j) direction]
    exact (Finset.disjoint_image g.injective).mpr (hdisjoint hij)
  · rw [hUnion, Finset.biUnion_image]
    simp only [LinearTransport.image_affineLine]

theorem inDirection_image_iff (g : Point p ≃ₗ[ZMod p] Point p)
    (S : Finset (Point p)) (direction : Point p) :
    IsCylinderInDirection p (S.image g) (g direction) ↔
      IsCylinderInDirection p S direction := by
  constructor
  · intro h
    have hback := inDirection_image p g.symm h
    simpa only [LinearTransport.image_symm_image, g.symm_apply_apply] using hback
  · exact inDirection_image p g

/-- Divisible coordinate fibres give a cylinder in the third direction itself. -/
theorem inVerticalDirection_of_fibreSize_dvd {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p S q) :
    IsCylinderInDirection p S (verticalDirection p) := by
  classical
  let e : Fin p ≃ activeProjections p S :=
    (Finset.equivFinOfCardEq (activeProjections_card p hcard hdiv)).symm
  let base : Fin p → Point p := fun i => lift p (e i).val 0
  refine ⟨verticalDirection_ne_zero p, base, ?_, ?_⟩
  · intro i j hij
    change Disjoint (affineLine p (lift p (e i).val 0) (verticalDirection p))
      (affineLine p (lift p (e j).val 0) (verticalDirection p))
    rw [← fullFibre_eq_affineLine, ← fullFibre_eq_affineLine]
    apply fullFibres_disjoint
    intro h
    exact hij (e.injective (Subtype.ext h))
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hfibre : x ∈ fibre p S (project p x) :=
        (mem_fibre p S (project p x) x).mpr ⟨hx, rfl⟩
      have hactive : project p x ∈ activeProjections p S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pos.mpr ⟨x, hfibre⟩⟩
      let q : activeProjections p S := ⟨project p x, hactive⟩
      refine ⟨e.symm q, ?_⟩
      change x ∈ affineLine p (lift p (e (e.symm q)).val 0) (verticalDirection p)
      rw [e.apply_symm_apply, ← fullFibre_eq_affineLine]
      exact (mem_fullFibre p q.val x).mpr rfl
    · rintro ⟨i, hi⟩
      change x ∈ affineLine p (lift p (e i).val 0) (verticalDirection p) at hi
      rw [← fullFibre_eq_affineLine, ← active_fibre_full p hdiv (e i).property] at hi
      exact ((mem_fibre p S (e i).val x).mp hi).1

/-- After normalising the given direction, the fibre conclusion transports back to that direction. -/
theorem inDirection_of_image_fibreSize_dvd (g : Point p ≃ₗ[ZMod p] Point p)
    {S : Finset (Point p)} {direction : Point p}
    (hgv : g direction = verticalDirection p) (hcard : S.card = p ^ 2)
    (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p (S.image g) q) :
    IsCylinderInDirection p S direction := by
  have hcard' : (S.image g).card = p ^ 2 := by
    simpa only [LinearTransport.image_card] using hcard
  have haxis := inVerticalDirection_of_fibreSize_dvd p hcard' hdiv
  apply (inDirection_image_iff p g S direction).mp
  simpa only [hgv] using haxis

#print axioms inDirection_image_iff
#print axioms fibreSize_image_eq_p_of_affineLine_subset
#print axioms inVerticalDirection_of_fibreSize_dvd
#print axioms inDirection_of_image_fibreSize_dvd

end Cylinder.DirectionCylinder
