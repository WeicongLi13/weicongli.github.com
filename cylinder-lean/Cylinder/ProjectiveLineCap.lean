module

public import Cylinder.ProjectivePlaneCap
public import Cylinder.ProjectiveBlackLine

/-!
# White-point and black-weight bounds on actual dual lines

For a black point outside a line, the joins to its white points lie
in a single actual dual plane. Distinct joins meet only at the black
point, so their white sets are disjoint. The plane cap and the proved
line balance yield the mixed cap, the white-line cap and the weight cap.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveLineCap

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.ProjectiveCover
open Cylinder.DualLineBalance Cylinder.ProjectiveBlackLine
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

theorem white_ne_black {S : Finset (Geometry.Point p)} {a b : DualPoint p}
    (ha : a ∈ whitePoints p S) (hb : b ∈ blackPoints p S) : a ≠ b := by
  have haq : quotient p S a = 0 := (Finset.mem_filter.mp ha).2
  have hbq : 2 ≤ quotient p S b := (Finset.mem_filter.mp hb).2
  intro h
  rw [h] at haq
  omega

theorem black_weight_pos {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : 1 ≤ weight p S b := by
  have hbq : 2 ≤ quotient p S b := (Finset.mem_filter.mp hb).2
  unfold weight
  omega

theorem outside_ne_on_line (W : Submodule (ZMod p) (DualSpace p))
    {b e : DualPoint p} (hb : b ∉ linePoints p W) (he : e.submodule ≤ W) : b ≠ e := by
  intro h
  subst e
  exact hb ((mem_linePoints p W b).mpr he)

theorem finrank_join_outside (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2) (b : DualPoint p) (hb : b ∉ linePoints p W) :
    Module.finrank (ZMod p) (W ⊔ b.submodule : Submodule (ZMod p) (DualSpace p)) = 3 := by
  have hrep : b.rep ∉ W := by
    intro h
    exact hb ((mem_linePoints p W b).mpr
      ((ProjectiveIncidence.submodule_le_iff_rep_mem b W).mpr h))
  rw [b.submodule_eq, Submodule.finrank_sup_span_singleton hrep, hW]

/-- Two distinct joins from an outside point to a fixed line meet only at that point. -/
theorem ray_inf_eq_point (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2) (b : DualPoint p) (hb : b ∉ linePoints p W)
    (e f : DualPoint p) (he : e.submodule ≤ W) (hf : f.submodule ≤ W) (hef : e ≠ f) :
    pairSpan p b e ⊓ pairSpan p b f = b.submodule := by
  have hbe := outside_ne_on_line p W hb he
  have hbf := outside_ne_on_line p W hb hf
  have hWspan : pairSpan p e f = W :=
    Submodule.eq_of_le_of_finrank_eq (pairSpan_le p e f W he hf)
      ((finrank_pairSpan p e f hef).trans hW.symm)
  have hsup : pairSpan p b e ⊔ pairSpan p b f = W ⊔ b.submodule := by
    apply le_antisymm
    · apply sup_le
      · exact pairSpan_le p b e _ le_sup_right (le_trans he le_sup_left)
      · exact pairSpan_le p b f _ le_sup_right (le_trans hf le_sup_left)
    · apply sup_le
      · rw [← hWspan]
        exact pairSpan_le p e f _ (le_trans (right_le_pairSpan p b e) le_sup_left)
          (le_trans (right_le_pairSpan p b f) le_sup_right)
      · exact le_trans (left_le_pairSpan p b e) le_sup_left
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (pairSpan p b e) (pairSpan p b f)
  rw [hsup, finrank_join_outside p W hW b hb, finrank_pairSpan p b e hbe,
    finrank_pairSpan p b f hbf] at hdim
  have hinf : Module.finrank (ZMod p)
      (pairSpan p b e ⊓ pairSpan p b f : Submodule (ZMod p) (DualSpace p)) = 1 := by omega
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
    (le_inf (left_le_pairSpan p b e) (left_le_pairSpan p b f))
  rw [Projectivization.finrank_submodule, hinf]

def whiteRay (S : Finset (Geometry.Point p)) (b e : DualPoint p) : Finset (DualPoint p) :=
  linePoints p (pairSpan p b e) ∩ whitePoints p S

theorem white_rays_disjoint {S : Finset (Geometry.Point p)}
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (b : DualPoint p) (hb : b ∈ blackPoints p S) (hbW : b ∉ linePoints p W)
    (e f : DualPoint p) (he : e.submodule ≤ W) (hf : f.submodule ≤ W) (hef : e ≠ f) :
    Disjoint (whiteRay p S b e) (whiteRay p S b f) := by
  apply Finset.disjoint_left.mpr
  intro H hHe hHf
  obtain ⟨hHeU, hwhite⟩ := Finset.mem_inter.mp hHe
  obtain ⟨hHfU, _hwhite⟩ := Finset.mem_inter.mp hHf
  have hHle : H.submodule ≤ b.submodule := by
    rw [← ray_inf_eq_point p W hW b hbW e f he hf hef]
    exact le_inf ((mem_linePoints p _ H).mp hHeU) ((mem_linePoints p _ H).mp hHfU)
  have hHb : H = b := Projectivization.submodule_injective
    (Submodule.eq_of_le_of_finrank_eq hHle (by simp only [Projectivization.finrank_submodule]))
  exact white_ne_black p hwhite hb hHb

/-- The mixed bound in Lemma `lem:linecap`, with actual point sets and weights. -/
theorem mixed_cap {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (b : DualPoint p) (hb : b ∈ blackPoints p S) (hbW : b ∉ linePoints p W) :
    (linePoints p W ∩ whitePoints p S).card * (weight p S b + 1) ≤ p - 1 := by
  let L := linePoints p W ∩ whitePoints p S
  let T := W ⊔ b.submodule
  have hT : Module.finrank (ZMod p) T = 3 := finrank_join_outside p W hW b hbW
  have hdisjoint : (L : Set (DualPoint p)).PairwiseDisjoint (whiteRay p S b) := by
    intro e he f hf hef
    obtain ⟨heW, _hewhite⟩ := Finset.mem_inter.mp he
    obtain ⟨hfW, _hfwhite⟩ := Finset.mem_inter.mp hf
    exact white_rays_disjoint p W hW b hb hbW e f
      ((mem_linePoints p W e).mp heW) ((mem_linePoints p W f).mp hfW) hef
  have hbound : ∀ e ∈ L, weight p S b + 1 ≤ (whiteRay p S b e).card := by
    intro e he
    obtain ⟨heW, hewhite⟩ := Finset.mem_inter.mp he
    have hbe := outside_ne_on_line p W hbW ((mem_linePoints p W e).mp heW)
    apply weight_add_one_le_white_on_line p hcard hS (pairSpan p b e)
      (finrank_pairSpan p b e hbe) _ b hb
      ((mem_linePoints p _ b).mpr (left_le_pairSpan p b e))
    exact ⟨e, Finset.mem_inter.mpr
      ⟨(mem_linePoints p _ e).mpr (right_le_pairSpan p b e), hewhite⟩⟩
  have hunion : L.biUnion (whiteRay p S b) ⊆
      whitePoints p S ∩ DualPlaneModel.dualPlanePoints p T := by
    intro H hH
    obtain ⟨e, he, hHe⟩ := Finset.mem_biUnion.mp hH
    obtain ⟨heW, _hewhite⟩ := Finset.mem_inter.mp he
    obtain ⟨hHeU, hwhite⟩ := Finset.mem_inter.mp hHe
    apply Finset.mem_inter.mpr
    refine ⟨hwhite, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact le_trans ((mem_linePoints p _ H).mp hHeU)
      (pairSpan_le p b e T le_sup_right (le_trans ((mem_linePoints p W e).mp heW) le_sup_left))
  calc
    (linePoints p W ∩ whitePoints p S).card * (weight p S b + 1) =
        ∑ _e ∈ L, (weight p S b + 1) := by simp only [Finset.sum_const_nat, L]
    _ ≤ ∑ e ∈ L, (whiteRay p S b e).card := Finset.sum_le_sum hbound
    _ = (L.biUnion (whiteRay p S b)).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ (whitePoints p S ∩ DualPlaneModel.dualPlanePoints p T).card := Finset.card_le_card hunion
    _ ≤ p - 1 := ProjectivePlaneCap.dual_plane_white_card_le p hcard hS hnon T hT

theorem line_white_card_le_half {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2) :
    (linePoints p W ∩ whitePoints p S).card ≤ (p - 1) / 2 := by
  obtain ⟨b, hb, hbW⟩ := exists_black_outside_line p hcard hS hnon W hW
  have hmix := mixed_cap p hcard hS hnon W hW b hb hbW
  have hweight : 2 ≤ weight p S b + 1 := by have h := black_weight_pos p hb; omega
  have hdouble := (Nat.mul_le_mul_left (linePoints p W ∩ whitePoints p S).card hweight).trans hmix
  omega

theorem black_weight_add_one_le_half {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (b : DualPoint p) (hb : b ∈ blackPoints p S) : weight p S b + 1 ≤ (p - 1) / 2 := by
  have hiwhite := infinity_mem_whitePoints p S
  have hbi : b ≠ infinity p := (white_ne_black p hiwhite hb).symm
  let W := pairSpan p b (infinity p)
  have hW : Module.finrank (ZMod p) W = 2 := finrank_pairSpan p b (infinity p) hbi
  have hwhite : (linePoints p W ∩ whitePoints p S).Nonempty :=
    ⟨infinity p, Finset.mem_inter.mpr
      ⟨(mem_linePoints p _ _).mpr (right_le_pairSpan p b (infinity p)), hiwhite⟩⟩
  exact (weight_add_one_le_white_on_line p hcard hS W hW hwhite b hb
    ((mem_linePoints p _ _).mpr (left_le_pairSpan p b (infinity p)))).trans
      (line_white_card_le_half p hcard hS hnon W hW)

theorem black_weight_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (b : DualPoint p) (hb : b ∈ blackPoints p S) : weight p S b ≤ (p - 3) / 2 := by
  have h := black_weight_add_one_le_half p hcard hS hnon b hb
  omega

/-- The line cap already settles the prime orders at most three. -/
theorem isCylinder_of_prime_le_three {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hp : p ≤ 3) : Geometry.IsCylinder p S := by
  by_contra hnon
  obtain ⟨b, hb⟩ := black_nonempty p hcard hS
  have hw := black_weight_pos p hb
  have hcap := black_weight_add_one_le_half p hcard hS hnon b hb
  omega

end Cylinder.ProjectiveLineCap

end
