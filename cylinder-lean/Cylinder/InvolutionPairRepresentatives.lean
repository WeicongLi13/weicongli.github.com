module

public import Cylinder.BMMMatchingParity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Canonical representatives of the actual pairs of a finite free
involution. Stable subsets and their sums are decomposed into real pairs. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.InvolutionPairRepresentatives

variable {I V : Type*} [Fintype I]

def rank (x : I) : Fin (Fintype.card I) := Fintype.equivFin I x

def pairRepresentatives (f : I → I) : Finset I :=
  Finset.univ.filter (fun x => rank x < rank (f x))

theorem mem_pairRepresentatives (f : I → I) (x : I) :
    x ∈ pairRepresentatives f ↔ rank x < rank (f x) := by
  simp only [pairRepresentatives, Finset.mem_filter, Finset.mem_univ, true_and]

theorem representative_partner_not_mem (f : I → I) (hinv : Function.Involutive f)
    (x : I) (hx : x ∈ pairRepresentatives f) : f x ∉ pairRepresentatives f := by
  rw [mem_pairRepresentatives] at hx ⊢
  rw [hinv]
  exact not_lt_of_gt hx

theorem stable_partition (f : I → I) (hinv : Function.Involutive f)
    (hfree : ∀ x, f x ≠ x) (S : Finset I) (hstable : ∀ x ∈ S, f x ∈ S) :
    let A := S.filter (fun x => rank x < rank (f x))
    Disjoint A (A.image f) ∧ A ∪ A.image f = S := by
  let A := S.filter (fun x => rank x < rank (f x))
  have hmem : ∀ x, x ∈ A ↔ x ∈ S ∧ rank x < rank (f x) := fun x => Finset.mem_filter
  have hother : ∀ x, x ∈ A.image f ↔ x ∈ S ∧ rank (f x) < rank x := by
    intro x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨hstable y (hmem y |>.mp hy).1, by simpa only [hinv y] using (hmem y |>.mp hy).2⟩
    · rintro ⟨hx, hr⟩
      exact Finset.mem_image.mpr ⟨f x, (hmem _).mpr ⟨hstable x hx, by simpa only [hinv x] using hr⟩, hinv x⟩
  refine ⟨Finset.disjoint_left.mpr (fun x hx hy => not_lt_of_gt ((hmem x).mp hx).2 ((hother x).mp hy).2), ?_⟩
  ext x
  rw [Finset.mem_union, hmem, hother]
  constructor
  · exact fun hx => hx.elim And.left And.left
  · intro hx
    have hn : rank x ≠ rank (f x) := fun he => hfree x ((Fintype.equivFin I).injective he.symm)
    exact (lt_or_gt_of_ne hn).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)

theorem stable_pair_card (f : I → I) (hinv : Function.Involutive f)
    (hfree : ∀ x, f x ≠ x) (S : Finset I) (hstable : ∀ x ∈ S, f x ∈ S) :
    2 * (S.filter (fun x => rank x < rank (f x))).card = S.card := by
  obtain ⟨hdisj, hcover⟩ := stable_partition f hinv hfree S hstable
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hcover, Finset.card_image_of_injective _ hinv.injective] at hc
  omega

theorem pairRepresentatives_card (f : I → I) (hinv : Function.Involutive f)
    (hfree : ∀ x, f x ≠ x) : 2 * (pairRepresentatives f).card = Fintype.card I := by
  simpa only [pairRepresentatives, Finset.card_univ] using
    stable_pair_card f hinv hfree Finset.univ (fun x _ => Finset.mem_univ (f x))

theorem pairRepresentatives_fiber_card {J : Type*} (f : I → I) (hinv : Function.Involutive f)
    (hfree : ∀ x, f x ≠ x) (k : I → J) (hk : ∀ x, k (f x) = k x) (a : J) :
    2 * ((pairRepresentatives f).filter (fun x => k x = a)).card =
      (Finset.univ.filter (fun x => k x = a)).card := by
  have hc := stable_pair_card f hinv hfree (Finset.univ.filter (fun x => k x = a)) (by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hk x).trans (Finset.mem_filter.mp hx).2⟩)
  have heq : (pairRepresentatives f).filter (fun x => k x = a) =
      (Finset.univ.filter (fun x => k x = a)).filter (fun x => rank x < rank (f x)) := by
    ext x
    simp only [pairRepresentatives, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  rw [heq]
  exact hc

theorem distinct_representative_pairs (f : I → I) (hinv : Function.Involutive f)
    (P Q : pairRepresentatives f) (hPQ : P ≠ Q) :
    P.val ≠ Q.val ∧ P.val ≠ f Q.val ∧ f P.val ≠ Q.val ∧ f P.val ≠ f Q.val := by
  have hne : P.val ≠ Q.val := fun h => hPQ (Subtype.ext h)
  have hcross : f P.val ≠ Q.val := by
    intro heq
    exact representative_partner_not_mem f hinv P.val P.property (heq ▸ Q.property)
  refine ⟨hne, ?_, hcross, fun h => hne (hinv.injective h)⟩
  intro heq
  exact hcross (by rw [heq, hinv])

theorem stable_sum_eq_sum_pairs [AddCommMonoid V] (f : I → I)
    (hinv : Function.Involutive f) (hfree : ∀ x, f x ≠ x)
    (S : Finset I) (hstable : ∀ x ∈ S, f x ∈ S) (v : I → V) :
    (∑ x ∈ S, v x) = ∑ x ∈ S.filter (fun x => rank x < rank (f x)), (v x + v (f x)) := by
  obtain ⟨hdisj, hcover⟩ := stable_partition f hinv hfree S hstable
  conv_lhs => rw [← hcover]
  rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hinv.injective h),
    ← Finset.sum_add_distrib]

end Cylinder.InvolutionPairRepresentatives
end
