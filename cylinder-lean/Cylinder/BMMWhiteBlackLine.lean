module

public import Cylinder.BMMActualBlackLineData

/-! A line through an actual white point contains at most one actual black
point. This uses the genuine white-to-blocker bijection and the arc bound. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMWhiteBlackLine

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData

variable {K : Type*} [Field K]

theorem collinear_partner_on_line (l : Fin 3 → K) (hl : l ≠ 0)
    (P Q R : PlanePoint K) (hPR : P ≠ R)
    (hP : dot l P.rep = 0) (hR : dot l R.rep = 0) (hcol : Collinear P Q R) :
    dot l Q.rep = 0 := by
  have hc := cross_ne_zero P.rep R.rep P.rep_nonzero (representatives_not_proportional P R hPR)
  obtain ⟨u, _hu, heq⟩ := annihilator_proportional l P.rep R.rep hl hc hP hR
  rw [heq]
  have hQ := collinear_line P Q R hcol
  simpa only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hQ, mul_zero]
    using congrArg (fun a : K => u * a) hQ

theorem arc_unique_on_line (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (l : Fin 3 → K) (hl : l ≠ 0) (P Q Q' : PlanePoint K)
    (hP : P ∈ W) (hQ : Q ∈ W) (hQ' : Q' ∈ W) (hPQ : P ≠ Q) (hPQ' : P ≠ Q')
    (hPl : dot l P.rep = 0) (hQl : dot l Q.rep = 0) (hQ'l : dot l Q'.rep = 0) : Q = Q' := by
  by_contra hQQ'
  have hsub : ({P, Q, Q'} : Finset (PlanePoint K)) ⊆ W.filter (fun X => dot l X.rep = 0) := by
    intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_filter.mpr ⟨hP, hPl⟩
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_filter.mpr ⟨hQ, hQl⟩
    have hXQ' := Finset.mem_singleton.mp hX
    subst X
    exact Finset.mem_filter.mpr ⟨hQ', hQ'l⟩
  have hcard : ({P, Q, Q'} : Finset (PlanePoint K)).card = 3 := by simp [hPQ, hPQ', hQQ']
  have hle := Finset.card_le_card hsub
  have hcap := hW l hl
  rw [hcard] at hle
  omega

theorem black_points_on_white_line_eq (A : Configuration K) (l : Fin 3 → K) (hl : l ≠ 0)
    (P : A.W) (hP : dot l P.val.rep = 0) (R S : A.B)
    (hR : dot l R.val.rep = 0) (hS : dot l S.val.rep = 0) : R = S := by
  let e := whiteBlockersEquiv A.W A.B A.arc A.disjoint A.blocks A.card P.val P.property
  let Q := e.symm R
  let Q' := e.symm S
  have hcolR : Collinear P.val Q.val R.val := by
    have h := blockerMap_collinear A.W A.B A.blocks P.val P.property Q
    change Collinear P.val Q.val (e Q).val at h
    simpa only [Q, e.apply_symm_apply] using h
  have hcolS : Collinear P.val Q'.val S.val := by
    have h := blockerMap_collinear A.W A.B A.blocks P.val P.property Q'
    change Collinear P.val Q'.val (e Q').val at h
    simpa only [Q', e.apply_symm_apply] using h
  have hPR : P.val ≠ R.val := by
    intro h
    exact Finset.disjoint_left.mp A.disjoint P.property (h ▸ R.property)
  have hPS : P.val ≠ S.val := by
    intro h
    exact Finset.disjoint_left.mp A.disjoint P.property (h ▸ S.property)
  have hQl := collinear_partner_on_line l hl P.val Q.val R.val hPR hP hR hcolR
  have hQ'l := collinear_partner_on_line l hl P.val Q'.val S.val hPS hP hS hcolS
  have hQQ' : Q = Q' := Subtype.ext (arc_unique_on_line A.W A.arc l hl P.val Q.val Q'.val
    P.property (Finset.mem_erase.mp Q.property).2 (Finset.mem_erase.mp Q'.property).2
    (Finset.mem_erase.mp Q.property).1.symm (Finset.mem_erase.mp Q'.property).1.symm hP hQl hQ'l)
  exact e.symm.injective hQQ'

theorem black_line_card_le_one (A : Configuration K) (l : Fin 3 → K) (hl : l ≠ 0)
    (P : A.W) (hP : dot l P.val.rep = 0) : (blackLine A l).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro R hR S hS
  obtain ⟨hRB, hRl⟩ := Finset.mem_filter.mp hR
  obtain ⟨hSB, hSl⟩ := Finset.mem_filter.mp hS
  exact congrArg Subtype.val (black_points_on_white_line_eq A l hl P hP ⟨R, hRB⟩ ⟨S, hSB⟩ hRl hSl)

theorem not_collinear_white_two_black (A : Configuration K) (P : A.W) (R S : A.B)
    (hRS : R ≠ S) : ¬ Collinear P.val R.val S.val := by
  intro hcol
  let l := cross R.val.rep S.val.rep
  have hl : l ≠ 0 := cross_ne_zero R.val.rep S.val.rep R.val.rep_nonzero
    (representatives_not_proportional R.val S.val (fun h => hRS (Subtype.ext h)))
  have hP : dot l P.val.rep = 0 := by
    have hcycle : dot (cross R.val.rep S.val.rep) P.val.rep =
        dot (cross P.val.rep R.val.rep) S.val.rep := by
      simp [dot, cross, Fin.sum_univ_succ]
      ring
    exact hcycle.trans hcol
  exact hRS (black_points_on_white_line_eq A l hl P hP R S
    (dot_cross_left R.val.rep S.val.rep) (dot_cross_right R.val.rep S.val.rep))

end Cylinder.BMMWhiteBlackLine

end
