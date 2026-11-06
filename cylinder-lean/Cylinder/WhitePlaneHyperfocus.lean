module

public import Cylinder.SimpleBlackWeights

/-! Actual white and black slices of dual subspaces, under the arc assumption.
No generalized-hyperfocus classification is assumed in this module. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.WhitePlaneHyperfocus

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.ProjectiveBlackLine Cylinder.ProjectiveLineCap

variable (p : ℕ) [Fact p.Prime]

def whiteSlice (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p)) :=
  linePoints p T ∩ whitePoints p S

def blackSlice (S : Finset (Geometry.Point p)) (T : Submodule (ZMod p) (DualSpace p)) :=
  linePoints p T ∩ blackPoints p S

def IsArc (S : Finset (Geometry.Point p)) : Prop :=
  ∀ L : Submodule (ZMod p) (DualSpace p), Module.finrank (ZMod p) L = 2 →
    (whiteSlice p S L).card ≤ 2

theorem slice_disjoint (S : Finset (Geometry.Point p))
    (T : Submodule (ZMod p) (DualSpace p)) :
    Disjoint (whiteSlice p S T) (blackSlice p S T) := by
  apply Finset.disjoint_left.mpr
  intro H hW hB
  exact white_ne_black p (Finset.mem_inter.mp hW).2 (Finset.mem_inter.mp hB).2 rfl

theorem line_card_balance {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (L : Submodule (ZMod p) (DualSpace p)) (hL : Module.finrank (ZMod p) L = 2)
    (hwhite : (whiteSlice p S L).Nonempty) :
    (blackSlice p S L).card + 1 = (whiteSlice p S L).card := by
  have hbalance := line_balance p hcard hS L hL hwhite
  have hsum : (∑ b ∈ blackSlice p S L, weight p S b) = (blackSlice p S L).card := by
    calc
      _ = ∑ _b ∈ blackSlice p S L, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact SimpleBlackWeights.black_weight_eq_one p hcard hS hnon (Finset.mem_inter.mp hb).2
      _ = _ := by simp
  change (∑ b ∈ blackSlice p S L, weight p S b) = (whiteSlice p S L).card - 1 at hbalance
  rw [hsum] at hbalance
  have hpos := Finset.card_pos.mpr hwhite
  omega

theorem pairSpan_eq_line (a b : DualPoint p) (hab : a ≠ b)
    (L : Submodule (ZMod p) (DualSpace p)) (hL : Module.finrank (ZMod p) L = 2)
    (ha : a.submodule ≤ L) (hb : b.submodule ≤ L) : pairSpan p a b = L :=
  Submodule.eq_of_le_of_finrank_eq (pairSpan_le p a b L ha hb)
    ((finrank_pairSpan p a b hab).trans hL.symm)

theorem arc_unique_other {S : Finset (Geometry.Point p)} (harc : IsArc p S)
    (a b c : DualPoint p) (hab : a ≠ b) (hac : a ≠ c)
    (ha : a ∈ whitePoints p S) (hb : b ∈ whitePoints p S) (hc : c ∈ whitePoints p S)
    (L : Submodule (ZMod p) (DualSpace p)) (hL : Module.finrank (ZMod p) L = 2)
    (haL : a.submodule ≤ L) (hbL : b.submodule ≤ L) (hcL : c.submodule ≤ L) : b = c := by
  by_contra hbc
  have hsub : ({a, b, c} : Finset (DualPoint p)) ⊆ whiteSlice p S L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x; exact Finset.mem_inter.mpr ⟨(mem_linePoints p L a).mpr haL, ha⟩
    · subst x; exact Finset.mem_inter.mpr ⟨(mem_linePoints p L b).mpr hbL, hb⟩
    · subst x; exact Finset.mem_inter.mpr ⟨(mem_linePoints p L c).mpr hcL, hc⟩
  have hcount := Finset.card_le_card hsub
  have hthree : ({a, b, c} : Finset (DualPoint p)).card = 3 := by simp [hab, hac, hbc]
  rw [hthree] at hcount
  have hcap := harc L hL
  omega

theorem arc_unique_black {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (L : Submodule (ZMod p) (DualSpace p)) (hL : Module.finrank (ZMod p) L = 2)
    (hwhite : (whiteSlice p S L).Nonempty)
    (b c : DualPoint p) (hb : b ∈ blackPoints p S) (hc : c ∈ blackPoints p S)
    (hbL : b.submodule ≤ L) (hcL : c.submodule ≤ L) : b = c := by
  have hbalance := line_card_balance p hcard hS hnon L hL hwhite
  have hcap := harc L hL
  apply (Finset.card_le_one.mp (show (blackSlice p S L).card ≤ 1 by omega))
  · exact Finset.mem_inter.mpr ⟨(mem_linePoints p L b).mpr hbL, hb⟩
  · exact Finset.mem_inter.mpr ⟨(mem_linePoints p L c).mpr hcL, hc⟩

theorem exists_other_white {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (a b : DualPoint p)
    (ha : a ∈ whitePoints p S) (hb : b ∈ blackPoints p S) :
    ∃ c ∈ whitePoints p S, c ≠ a ∧ c.submodule ≤ pairSpan p a b := by
  have hab := white_ne_black p ha hb
  have haL : a ∈ whiteSlice p S (pairSpan p a b) :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p _ a).mpr (left_le_pairSpan p a b), ha⟩
  have hw := black_weight_pos p hb
  have hbound := weight_add_one_le_white_on_line p hcard hS (pairSpan p a b)
    (finrank_pairSpan p a b hab) ⟨a, haL⟩ b hb
    ((mem_linePoints p _ b).mpr (right_le_pairSpan p a b))
  change weight p S b + 1 ≤ (whiteSlice p S (pairSpan p a b)).card at hbound
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne (show 1 < (whiteSlice p S (pairSpan p a b)).card by omega) a
  exact ⟨c, (Finset.mem_inter.mp hc).2, hca,
    (mem_linePoints p _ c).mp (Finset.mem_inter.mp hc).1⟩

theorem secant_blocker_in_slice {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (T : Submodule (ZMod p) (DualSpace p))
    (a b : DualPoint p) (ha : a ∈ whiteSlice p S T) (hb : b ∈ whiteSlice p S T)
    (hab : a ≠ b) :
    ∃ c ∈ blackSlice p S T, c.submodule ≤ pairSpan p a b := by
  obtain ⟨c, hc, hcL⟩ := exists_black_of_two_white p hcard hS (pairSpan p a b)
    (finrank_pairSpan p a b hab) a b hab (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    (left_le_pairSpan p a b) (right_le_pairSpan p a b)
  refine ⟨c, Finset.mem_inter.mpr ⟨(mem_linePoints p T c).mpr ?_, hc⟩, hcL⟩
  exact le_trans hcL (pairSpan_le p a b T
    ((mem_linePoints p T a).mp (Finset.mem_inter.mp ha).1)
    ((mem_linePoints p T b).mp (Finset.mem_inter.mp hb).1))

def blockerMap {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (T : Submodule (ZMod p) (DualSpace p))
    (a : DualPoint p) (ha : a ∈ whiteSlice p S T) :
    (whiteSlice p S T).erase a → blackSlice p S T := fun b =>
  let hex := secant_blocker_in_slice p hcard hS T a b.val ha
    (Finset.mem_erase.mp b.property).2 (Finset.mem_erase.mp b.property).1.symm
  ⟨hex.choose, hex.choose_spec.1⟩

theorem blockerMap_spec {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (T : Submodule (ZMod p) (DualSpace p))
    (a : DualPoint p) (ha : a ∈ whiteSlice p S T) (b : (whiteSlice p S T).erase a) :
    (blockerMap p hcard hS T a ha b).val.submodule ≤ pairSpan p a b.val := by
  exact (secant_blocker_in_slice p hcard hS T a b.val ha
    (Finset.mem_erase.mp b.property).2 (Finset.mem_erase.mp b.property).1.symm).choose_spec.2

theorem blockerMap_bijective {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (a : DualPoint p) (ha : a ∈ whiteSlice p S T) :
    Function.Bijective (blockerMap p hcard hS T a ha) := by
  have haW := (Finset.mem_inter.mp ha).2
  have haT := (mem_linePoints p T a).mp (Finset.mem_inter.mp ha).1
  constructor
  · intro b c heq
    let z := blockerMap p hcard hS T a ha b
    have hzB := (Finset.mem_inter.mp z.property).2
    have haz := white_ne_black p haW hzB
    have hbne := (Finset.mem_erase.mp b.property).1.symm
    have hcne := (Finset.mem_erase.mp c.property).1.symm
    have hbspan : pairSpan p a z.val = pairSpan p a b.val := pairSpan_eq_line p a z.val haz _
      (finrank_pairSpan p a b.val hbne) (left_le_pairSpan p a b.val)
      (blockerMap_spec p hcard hS T a ha b)
    have hcspan : pairSpan p a z.val = pairSpan p a c.val := pairSpan_eq_line p a z.val haz _
      (finrank_pairSpan p a c.val hcne) (left_le_pairSpan p a c.val)
      (by simpa only [z, ← heq] using blockerMap_spec p hcard hS T a ha c)
    apply Subtype.ext
    apply arc_unique_other p harc a b.val c.val hbne hcne haW
      (Finset.mem_inter.mp (Finset.mem_erase.mp b.property).2).2
      (Finset.mem_inter.mp (Finset.mem_erase.mp c.property).2).2
      (pairSpan p a z.val) (finrank_pairSpan p a z.val haz) (left_le_pairSpan p a z.val)
    · rw [hbspan]; exact right_le_pairSpan p a b.val
    · rw [hcspan]; exact right_le_pairSpan p a c.val
  · intro z
    have hzB := (Finset.mem_inter.mp z.property).2
    have hzT := (mem_linePoints p T z.val).mp (Finset.mem_inter.mp z.property).1
    obtain ⟨b, hb, hbne, hbL⟩ := exists_other_white p hcard hS a z.val haW hzB
    have hbT := le_trans hbL (pairSpan_le p a z.val T haT hzT)
    let b' : (whiteSlice p S T).erase a := ⟨b, Finset.mem_erase.mpr
      ⟨hbne, Finset.mem_inter.mpr ⟨(mem_linePoints p T b).mpr hbT, hb⟩⟩⟩
    refine ⟨b', Subtype.ext ?_⟩
    have haz := white_ne_black p haW hzB
    have hspan := pairSpan_eq_line p a b hbne.symm (pairSpan p a z.val)
      (finrank_pairSpan p a z.val haz) (left_le_pairSpan p a z.val) hbL
    apply arc_unique_black p hcard hS hnon harc (pairSpan p a z.val)
      (finrank_pairSpan p a z.val haz)
      ⟨a, Finset.mem_inter.mpr ⟨(mem_linePoints p _ a).mpr (left_le_pairSpan p a z.val), haW⟩⟩
      _ z.val (Finset.mem_inter.mp (blockerMap p hcard hS T a ha b').property).2 hzB
    · rw [← hspan]; exact blockerMap_spec p hcard hS T a ha b'
    · exact right_le_pairSpan p a z.val

theorem slice_card_balance {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hwhite : (whiteSlice p S T).Nonempty) :
    (blackSlice p S T).card + 1 = (whiteSlice p S T).card := by
  obtain ⟨a, ha⟩ := hwhite
  have hc := Fintype.card_congr (Equiv.ofBijective (blockerMap p hcard hS T a ha)
    (blockerMap_bijective p hcard hS hnon harc T a ha))
  simp only [Fintype.card_coe, Finset.card_erase_of_mem ha] at hc
  have hpos := Finset.card_pos.mpr ⟨a, ha⟩
  omega

end Cylinder.WhitePlaneHyperfocus

end
