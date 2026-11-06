module

public import Cylinder.RationalPlaneLine
public import Mathlib.Data.Fintype.Card

/-! Actual secants and blocker matchings for finite projective plane arcs.
The classification theorem is not assumed or asserted here. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMArcGeometry

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct

variable {K : Type*} [Field K]

def Collinear (P Q R : PlanePoint K) : Prop := dot (cross P.rep Q.rep) R.rep = 0

def BlocksSecants (W B : Finset (PlanePoint K)) : Prop :=
  ∀ P ∈ W, ∀ Q ∈ W, P ≠ Q → ∃ R ∈ B, Collinear P Q R

theorem triple_swap (v w z : Fin 3 → K) : dot (cross v w) z = -dot (cross v z) w := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

theorem collinear_swap (P Q R : PlanePoint K) (h : Collinear P Q R) : Collinear Q P R := by
  change dot (cross Q.rep P.rep) R.rep = 0
  have he : dot (cross Q.rep P.rep) R.rep = -dot (cross P.rep Q.rep) R.rep := by
    simp [dot, cross, Fin.sum_univ_succ]
    ring
  rw [he, h, neg_zero]

theorem collinear_line (P Q R : PlanePoint K) (h : Collinear P Q R) :
    dot (cross P.rep R.rep) Q.rep = 0 := by
  have hh := triple_swap P.rep Q.rep R.rep
  rw [h] at hh
  exact neg_eq_zero.mp hh.symm

theorem arc_unique_other (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (P Q Q' R : PlanePoint K) (hP : P ∈ W) (hQ : Q ∈ W) (hQ' : Q' ∈ W)
    (hPQ : P ≠ Q) (hPQ' : P ≠ Q') (hPR : P ≠ R)
    (hQR : Collinear P Q R) (hQ'R : Collinear P Q' R) : Q = Q' := by
  by_contra hQQ'
  let c := cross P.rep R.rep
  have hc : c ≠ 0 := cross_ne_zero P.rep R.rep P.rep_nonzero
    (representatives_not_proportional P R hPR)
  have hPc : dot c P.rep = 0 := dot_cross_left P.rep R.rep
  have hQc : dot c Q.rep = 0 := collinear_line P Q R hQR
  have hQ'c : dot c Q'.rep = 0 := collinear_line P Q' R hQ'R
  have hsub : ({P, Q, Q'} : Finset (PlanePoint K)) ⊆ W.filter (fun X => dot c X.rep = 0) := by
    intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_filter.mpr ⟨hP, hPc⟩
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_filter.mpr ⟨hQ, hQc⟩
    have hXQ' := Finset.mem_singleton.mp hX
    subst X
    exact Finset.mem_filter.mpr ⟨hQ', hQ'c⟩
  have hcard : ({P, Q, Q'} : Finset (PlanePoint K)).card = 3 := by
    simp [hPQ, hPQ', hQQ']
  have hle := Finset.card_le_card hsub
  have hcap := hW c hc
  rw [hcard] at hle
  omega

def blockerMap (W B : Finset (PlanePoint K)) (hblock : BlocksSecants W B)
    (P : PlanePoint K) (hP : P ∈ W) : W.erase P → B := fun Q =>
  let hex := hblock P hP Q.val (Finset.mem_erase.mp Q.property).2
    (Finset.mem_erase.mp Q.property).1.symm
  ⟨hex.choose, hex.choose_spec.1⟩

theorem blockerMap_collinear (W B : Finset (PlanePoint K)) (hblock : BlocksSecants W B)
    (P : PlanePoint K) (hP : P ∈ W) (Q : W.erase P) :
    Collinear P Q.val (blockerMap W B hblock P hP Q).val := by
  exact (hblock P hP Q.val (Finset.mem_erase.mp Q.property).2
    (Finset.mem_erase.mp Q.property).1.symm).choose_spec.2

theorem blockerMap_injective (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B)
    (P : PlanePoint K) (hP : P ∈ W) : Function.Injective (blockerMap W B hblock P hP) := by
  intro Q Q' heq
  let R := blockerMap W B hblock P hP Q
  have hPR : P ≠ R.val := by
    intro h
    exact Finset.disjoint_left.mp hdisj hP (h ▸ R.property)
  apply Subtype.ext
  exact arc_unique_other W hW P Q.val Q'.val R.val hP
    (Finset.mem_erase.mp Q.property).2 (Finset.mem_erase.mp Q'.property).2
    (Finset.mem_erase.mp Q.property).1.symm (Finset.mem_erase.mp Q'.property).1.symm hPR
    (blockerMap_collinear W B hblock P hP Q)
    (by simpa only [R, ← heq] using blockerMap_collinear W B hblock P hP Q')

theorem blockerMap_bijective (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P : PlanePoint K) (hP : P ∈ W) : Function.Bijective (blockerMap W B hblock P hP) := by
  have hcards : Fintype.card (W.erase P) = Fintype.card B := by
    simp only [Fintype.card_coe, Finset.card_erase_of_mem hP]
    omega
  let E : W.erase P ≃ B := Fintype.equivOfCardEq hcards
  have hinj := blockerMap_injective W B hW hdisj hblock P hP
  exact ⟨hinj, (Finite.injective_iff_surjective_of_equiv E).mp hinj⟩

def whiteBlockersEquiv (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P : PlanePoint K) (hP : P ∈ W) : W.erase P ≃ B :=
  Equiv.ofBijective (blockerMap W B hblock P hP)
    (blockerMap_bijective W B hW hdisj hblock hcard P hP)

theorem exists_unique_partner (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (P : PlanePoint K) (hP : P ∈ W) (R : B) :
    ∃! Q : W, Q.val ≠ P ∧ Collinear P Q.val R.val := by
  obtain ⟨Q, hQR⟩ := (blockerMap_bijective W B hW hdisj hblock hcard P hP).2 R
  refine ⟨⟨Q.val, (Finset.mem_erase.mp Q.property).2⟩,
    ⟨(Finset.mem_erase.mp Q.property).1, ?_⟩, ?_⟩
  · simpa only [hQR] using blockerMap_collinear W B hblock P hP Q
  · intro Q' hQ'
    have hPR : P ≠ R.val := by
      intro h
      exact Finset.disjoint_left.mp hdisj hP (h ▸ R.property)
    apply Subtype.ext
    exact arc_unique_other W hW P Q'.val Q.val R.val hP Q'.property
      (Finset.mem_erase.mp Q.property).2 hQ'.1.symm
      (Finset.mem_erase.mp Q.property).1.symm hPR hQ'.2
      (by simpa only [hQR] using blockerMap_collinear W B hblock P hP Q)

def blackPartner (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (R : B) (P : W) : W :=
  (exists_unique_partner W B hW hdisj hblock hcard P.val P.property R).choose

theorem blackPartner_spec (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (R : B) (P : W) :
    (blackPartner W B hW hdisj hblock hcard R P).val ≠ P.val ∧
      Collinear P.val (blackPartner W B hW hdisj hblock hcard R P).val R.val :=
  (exists_unique_partner W B hW hdisj hblock hcard P.val P.property R).choose_spec.1

theorem blackPartner_ne (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (R : B) (P : W) : blackPartner W B hW hdisj hblock hcard R P ≠ P := by
  intro h
  exact (blackPartner_spec W B hW hdisj hblock hcard R P).1 (congrArg Subtype.val h)

theorem blackPartner_involutive (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (R : B) : Function.Involutive (blackPartner W B hW hdisj hblock hcard R) := by
  intro P
  let Q := blackPartner W B hW hdisj hblock hcard R P
  have hPQ := blackPartner_spec W B hW hdisj hblock hcard R P
  have hex := exists_unique_partner W B hW hdisj hblock hcard Q.val Q.property R
  have hfirst : blackPartner W B hW hdisj hblock hcard R Q = hex.choose :=
    hex.choose_spec.2 _ (blackPartner_spec W B hW hdisj hblock hcard R Q)
  have hsecond : P = hex.choose := hex.choose_spec.2 P
    ⟨hPQ.1.symm, collinear_swap P.val Q.val R.val hPQ.2⟩
  exact hfirst.trans hsecond.symm

end Cylinder.BMMArcGeometry

end
