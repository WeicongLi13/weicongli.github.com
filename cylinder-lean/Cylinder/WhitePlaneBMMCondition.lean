module

public import Cylinder.WhitePlaneCoordinates

/-! This file states the BMM classification as an explicit proposition,
and connects that proposition to the actual dual slices. It does not prove
or assume an axiom for the classification. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WhitePlaneBMMCondition

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.WhitePlaneHyperfocus Cylinder.WhitePlaneCoordinates Cylinder.RationalPlaneLine

variable (p : ℕ) [Fact p.Prime]

def BMMClassification : Prop :=
  ∀ W B : Finset (PlanePoint (ZMod p)), LineCap W 2 → Disjoint W B →
    BMMArcGeometry.BlocksSecants W B → B.card + 1 = W.card → 2 ≤ W.card →
    W.card = 2 ∨ W.card = 4

theorem actual_plane_two_or_four (hBMM : BMMClassification p)
    {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3)
    (hk : 2 ≤ (whiteSlice p S T).card) :
    (whiteSlice p S T).card = 2 ∨ (whiteSlice p S T).card = 4 := by
  obtain ⟨hW, hd, hb, hc⟩ := actual_generalized_hyperfocus p hcard hS hnon harc T hT
    (Finset.card_pos.mp (by omega))
  have h := hBMM (planeWhite p S T hT) (planeBlack p S T hT) hW hd hb hc
    (by rwa [planeWhite_card])
  simpa only [planeWhite_card] using h

theorem actual_plane_white_cap_four (hBMM : BMMClassification p)
    {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (harc : IsArc p S)
    (T : Submodule (ZMod p) (DualSpace p)) (hT : Module.finrank (ZMod p) T = 3) :
    (whiteSlice p S T).card ≤ 4 := by
  by_cases hk : 2 ≤ (whiteSlice p S T).card
  · rcases actual_plane_two_or_four p hBMM hcard hS hnon harc T hT hk with h | h <;> omega
  · omega

end Cylinder.WhitePlaneBMMCondition

end
