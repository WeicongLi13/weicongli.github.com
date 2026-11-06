module

public import Cylinder.BMMArcGeometry
public import Mathlib.Algebra.Ring.Parity

/-! Blocker matchings partition actual white points into pairs. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMMatchingParity

theorem fixed_point_free_involution_even_card {I : Type*} [Fintype I]
    (f : I → I) (hinv : Function.Involutive f) (hfree : ∀ x, f x ≠ x) :
    Even (Fintype.card I) := by
  let e := Fintype.equivFin I
  let A : Finset I := Finset.univ.filter (fun x => e x < e (f x))
  let B : Finset I := Finset.univ.filter (fun x => e (f x) < e x)
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have ha := (Finset.mem_filter.mp hxA).2
    have hb := (Finset.mem_filter.mp hxB).2
    exact (not_lt_of_gt ha) hb
  have hcover : A ∪ B = Finset.univ := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_gt_of_ne (fun h => hfree x (e.injective h.symm))
  have himage : A.image f = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hinv x] using (Finset.mem_filter.mp hx).2⟩
    · intro hy
      apply Finset.mem_image.mpr
      refine ⟨f y, ?_, hinv y⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hinv y] using (Finset.mem_filter.mp hy).2⟩
  have hcards : A.card = B.card := by
    rw [← himage, Finset.card_image_of_injective _ hinv.injective]
  have htotal := Finset.card_union_of_disjoint hdisj
  rw [hcover, Finset.card_univ, ← hcards] at htotal
  exact ⟨A.card, htotal⟩

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry

variable {K : Type*} [Field K]

theorem white_card_even (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (hk : 2 ≤ W.card) : Even W.card := by
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  let R : B := ⟨hB.choose, hB.choose_spec⟩
  have heven := fixed_point_free_involution_even_card
    (blackPartner W B hW hdisj hblock hcard R)
    (blackPartner_involutive W B hW hdisj hblock hcard R)
    (blackPartner_ne W B hW hdisj hblock hcard R)
  simpa only [Fintype.card_coe] using heven

theorem white_card_twice (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (hk : 2 ≤ W.card) : ∃ n : ℕ, 1 ≤ n ∧ W.card = 2 * n := by
  obtain ⟨n, hn⟩ := white_card_even W B hW hdisj hblock hcard hk
  exact ⟨n, by omega, by omega⟩

end Cylinder.BMMMatchingParity

end
