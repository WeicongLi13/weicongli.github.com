module

public import Cylinder.WhitePlaneBMMCondition
public import Cylinder.WhiteLinePlaneCounting

/-! The actual finite-projective counting proof of `lem:notcap`, conditional
only on the explicitly named BMM classification proposition. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WhiteNotCapCondition

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.ProjectiveBlackLine Cylinder.WhitePlaneHyperfocus Cylinder.WhitePlaneBMMCondition

variable (p : ℕ) [Fact p.Prime]

theorem white_not_isArc_of_bmm (hBMM : BMMClassification p)
    {S : Finset (Geometry.Point p)} (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) : ¬IsArc p S := by
  intro harc
  have hn := SimpleBlackWeights.white_card_exact p hcard hS hnon
  have hproduct : 5 * p ≤ p * (p - 1) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    have hm : 10 ≤ p - 1 := by omega
    nlinarith
  have hwhiteLarge : 1 < (whitePoints p S).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hwhiteLarge
  let L := pairSpan p a b
  have hL : Module.finrank (ZMod p) L = 2 := finrank_pairSpan p a b hab
  have hpair : ({a, b} : Finset (DualPoint p)) ⊆ whitePoints p S ∩ linePoints p L := by
    intro H hH
    rcases Finset.mem_insert.mp hH with h | h
    · subst H
      exact Finset.mem_inter.mpr ⟨ha, (mem_linePoints p L a).mpr (left_le_pairSpan p a b)⟩
    · have hHb := Finset.mem_singleton.mp h
      subst H
      exact Finset.mem_inter.mpr ⟨hb, (mem_linePoints p L b).mpr (right_le_pairSpan p a b)⟩
  have htwo := Finset.card_le_card hpair
  have hpaircard : ({a, b} : Finset (DualPoint p)).card = 2 := by simp [hab]
  rw [hpaircard] at htwo
  have hcap : (whitePoints p S ∩ linePoints p L).card ≤ 2 := by
    simpa only [whiteSlice, Finset.inter_comm] using harc L hL
  have hline : (whitePoints p S ∩ linePoints p L).card = 2 := by omega
  have hplanes : ∀ T : Submodule (ZMod p) (DualSpace p), Module.finrank (ZMod p) T = 3 →
      L ≤ T → (whitePoints p S ∩ linePoints p T).card ≤ 4 := by
    intro T hT _hLT
    simpa only [whiteSlice, Finset.inter_comm] using
      actual_plane_white_cap_four p hBMM hcard hS hnon harc T hT
  have htotal := WhiteLinePlaneCounting.card_le_two_prime_add_four p (whitePoints p S) L hL hline hplanes
  omega

theorem exists_three_collinear_white_of_bmm (hBMM : BMMClassification p)
    {S : Finset (Geometry.Point p)} (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S) :
    ∃ L : Submodule (ZMod p) (DualSpace p), Module.finrank (ZMod p) L = 2 ∧
      ∃ a b c : DualPoint p, a ∈ whiteSlice p S L ∧ b ∈ whiteSlice p S L ∧
        c ∈ whiteSlice p S L ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hnot := white_not_isArc_of_bmm p hBMM hp hcard hS hnon
  unfold IsArc at hnot
  push Not at hnot
  obtain ⟨L, hL, hk⟩ := hnot
  exact ⟨L, hL, Finset.two_lt_card_iff.mp hk⟩

end Cylinder.WhiteNotCapCondition

end
