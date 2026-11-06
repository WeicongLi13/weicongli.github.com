module

public import Cylinder.ProjectiveCoplanarity
public import Cylinder.DualLineBalance
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A collinear black configuration forces a cylinder

Two distinct white points determine an actual projective line. Line
balance forces a black point on that line. If all black points belong
to a fixed line, every white point belongs to the span of that line
and any white point outside it. This span has dimension at most three.
Its nonzero primal coannihilator gives the required common point of
all empty planes.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveBlackLine

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.ProjectiveCover Cylinder.ProjectiveCoplanarity Cylinder.DualLineBalance
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def pairSpan (a b : DualPoint p) : Submodule (ZMod p) (DualSpace p) :=
  Submodule.span (ZMod p) (Set.range ![a.rep, b.rep])

theorem left_le_pairSpan (a b : DualPoint p) : a.submodule ≤ pairSpan p a b := by
  rw [ProjectiveIncidence.submodule_le_iff_rep_mem]
  exact Submodule.subset_span (Set.mem_range.mpr ⟨(0 : Fin 2), rfl⟩)

theorem right_le_pairSpan (a b : DualPoint p) : b.submodule ≤ pairSpan p a b := by
  rw [ProjectiveIncidence.submodule_le_iff_rep_mem]
  exact Submodule.subset_span (Set.mem_range.mpr ⟨(1 : Fin 2), rfl⟩)

theorem pairSpan_le (a b : DualPoint p) (W : Submodule (ZMod p) (DualSpace p))
    (ha : a.submodule ≤ W) (hb : b.submodule ≤ W) : pairSpan p a b ≤ W := by
  have ha' := (ProjectiveIncidence.submodule_le_iff_rep_mem a W).mp ha
  have hb' := (ProjectiveIncidence.submodule_le_iff_rep_mem b W).mp hb
  simpa [pairSpan, Submodule.span_le, Set.range_subset_iff, Fin.forall_fin_two,
    Set.insert_subset_iff, Set.singleton_subset_iff, and_comm] using And.intro ha' hb'

theorem finrank_pairSpan (a b : DualPoint p) (hab : a ≠ b) :
    Module.finrank (ZMod p) (pairSpan p a b) = 2 := by
  have hlin := (Projectivization.linearIndependent_pair_iff_ne (D := a) (D' := b)).mpr hab
  unfold pairSpan
  simpa only [Fintype.card_fin] using finrank_span_eq_card hlin

/-- Any actual dual line containing two distinct white points contains a black point. -/
theorem exists_black_of_two_white {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (a b : DualPoint p) (hab : a ≠ b)
    (ha : a ∈ whitePoints p S) (hb : b ∈ whitePoints p S)
    (haW : a.submodule ≤ W) (hbW : b.submodule ≤ W) :
    ∃ c ∈ blackPoints p S, c.submodule ≤ W := by
  have haI : a ∈ linePoints p W ∩ whitePoints p S :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p W a).mpr haW, ha⟩
  have hbI : b ∈ linePoints p W ∩ whitePoints p S :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p W b).mpr hbW, hb⟩
  have hsub : ({a, b} : Finset (DualPoint p)) ⊆ linePoints p W ∩ whitePoints p S := by
    intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact haI
    · exact hbI
  have htwo := Finset.card_le_card hsub
  have hpaircard : ({a, b} : Finset (DualPoint p)).card = 2 := by simp [hab]
  rw [hpaircard] at htwo
  have hbalance := line_balance p hcard hS W hW ⟨a, haI⟩
  rcases (linePoints p W ∩ blackPoints p S).eq_empty_or_nonempty with hempty | hblack
  · rw [hempty, Finset.sum_empty] at hbalance
    omega
  · obtain ⟨c, hc⟩ := hblack
    obtain ⟨hcW, hcB⟩ := Finset.mem_inter.mp hc
    exact ⟨c, hcB, (mem_linePoints p W c).mp hcW⟩

/-- A dual subspace of dimension at most three has a nonzero primal coannihilator. -/
theorem whiteCoplanar_of_submodule {S : Finset (Geometry.Point p)}
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T ≤ 3)
    (hwhite : ∀ H ∈ whitePoints p S, H.submodule ≤ T) : WhiteCoplanar p S := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq T
  have hV : Module.finrank (ZMod p) (ProjectiveGeometry.Vector p) = 4 := by
    simp [ProjectiveGeometry.Vector]
  rw [hV] at hdim
  change Module.finrank (ZMod p) T + Module.finrank (ZMod p) T.dualCoannihilator = 4 at hdim
  have hpos : 0 < Module.finrank (ZMod p) T.dualCoannihilator := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv' : (v : ProjectiveGeometry.Vector p) ≠ 0 := Subtype.coe_injective.ne hv
  refine ⟨Projectivization.mk (ZMod p) (v : ProjectiveGeometry.Vector p) hv', ?_⟩
  intro H hH
  apply (incident_mk_rep_iff p _ hv' H).mpr
  have hmem : H.rep ∈ T :=
    (ProjectiveIncidence.submodule_le_iff_rep_mem H T).mp (hwhite H hH)
  exact ((Submodule.mem_dualCoannihilator (v : ProjectiveGeometry.Vector p)).mp v.property) H.rep hmem

/-- All black points lying on an actual dual projective line forces white coplanarity. -/
theorem whiteCoplanar_of_black_on_line {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (hblack : ∀ H ∈ blackPoints p S, H.submodule ≤ W) : WhiteCoplanar p S := by
  by_cases hwhite : ∀ H ∈ whitePoints p S, H.submodule ≤ W
  · exact whiteCoplanar_of_submodule p W (by omega) hwhite
  push Not at hwhite
  obtain ⟨a, ha, haW⟩ := hwhite
  let T := W ⊔ a.submodule
  have hT : Module.finrank (ZMod p) T ≤ 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W a.submodule
    rw [hW, Projectivization.finrank_submodule] at h
    change Module.finrank (ZMod p) (W ⊔ a.submodule : Submodule (ZMod p) (DualSpace p)) ≤ 3
    omega
  apply whiteCoplanar_of_submodule p T hT
  intro b hb
  by_cases hab : a = b
  · subst b
    exact le_sup_right
  let U := pairSpan p a b
  have hU : Module.finrank (ZMod p) U = 2 := finrank_pairSpan p a b hab
  obtain ⟨c, hcB, hcU⟩ := exists_black_of_two_white p hcard hS U hU a b hab ha hb
    (left_le_pairSpan p a b) (right_le_pairSpan p a b)
  have hcW := hblack c hcB
  have hac : a ≠ c := by
    intro h
    subst c
    exact haW hcW
  have hspan : pairSpan p a c = U := by
    apply Submodule.eq_of_le_of_finrank_eq
      (pairSpan_le p a c U (left_le_pairSpan p a b) hcU)
    rw [finrank_pairSpan p a c hac, hU]
  calc
    b.submodule ≤ U := right_le_pairSpan p a b
    _ = pairSpan p a c := hspan.symm
    _ ≤ T := pairSpan_le p a c T le_sup_right (le_trans hcW le_sup_left)

/-- The last assertion of Lemma `lem:coplanarity`. -/
theorem isCylinder_of_black_on_line {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (hblack : ∀ H ∈ blackPoints p S, H.submodule ≤ W) : Geometry.IsCylinder p S :=
  isCylinder_of_whiteCoplanar p hcard hS (whiteCoplanar_of_black_on_line p hcard hS W hW hblack)

def BlackCollinear (S : Finset (Geometry.Point p)) : Prop :=
  ∃ W : Submodule (ZMod p) (DualSpace p), Module.finrank (ZMod p) W = 2 ∧
    ∀ H ∈ blackPoints p S, H.submodule ≤ W

theorem isCylinder_of_blackCollinear {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hblack : BlackCollinear p S) :
    Geometry.IsCylinder p S := by
  obtain ⟨W, hW, hB⟩ := hblack
  exact isCylinder_of_black_on_line p hcard hS W hW hB

theorem not_blackCollinear_of_not_isCylinder {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S) :
    ¬ BlackCollinear p S := fun h => hnon (isCylinder_of_blackCollinear p hcard hS h)

/-- Every actual dual line has a black point outside it for a noncylinder. -/
theorem exists_black_outside_line {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2) :
    ∃ H ∈ blackPoints p S, H ∉ linePoints p W := by
  by_contra h
  push Not at h
  apply hnon
  apply isCylinder_of_black_on_line p hcard hS W hW
  intro H hH
  exact (mem_linePoints p W H).mp (h H hH)

/-- A black point on a line with a white point forces at least its weight plus one white points. -/
theorem weight_add_one_le_white_on_line {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (hwhite : (linePoints p W ∩ whitePoints p S).Nonempty)
    (H : DualPoint p) (hH : H ∈ blackPoints p S) (hHW : H ∈ linePoints p W) :
    weight p S H + 1 ≤ (linePoints p W ∩ whitePoints p S).card := by
  have hmem : H ∈ linePoints p W ∩ blackPoints p S := Finset.mem_inter.mpr ⟨hHW, hH⟩
  have hle : weight p S H ≤ ∑ K ∈ linePoints p W ∩ blackPoints p S, weight p S K :=
    Finset.single_le_sum (fun K _ => Nat.zero_le (weight p S K)) hmem
  rw [line_balance p hcard hS W hW hwhite] at hle
  have hpos := Finset.card_pos.mpr hwhite
  omega

#print axioms exists_black_of_two_white
#print axioms whiteCoplanar_of_submodule
#print axioms isCylinder_of_blackCollinear
#print axioms exists_black_outside_line
#print axioms weight_add_one_le_white_on_line

end Cylinder.ProjectiveBlackLine

end
