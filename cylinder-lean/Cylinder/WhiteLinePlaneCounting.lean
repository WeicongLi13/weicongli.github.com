module

public import Cylinder.WhitePlaneHyperfocus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual quotient directions index the planes through a fixed dual line. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Cylinder.WhiteLinePlaneCounting

open Module Cylinder.ProjectiveGeometry Cylinder.DualLineBalance

variable (p : ℕ) [Fact p.Prime]

abbrev PlaneIndex (L : Submodule (ZMod p) (DualSpace p)) :=
  Projectivization (ZMod p) (DualSpace p ⧸ L)

instance (L : Submodule (ZMod p) (DualSpace p)) : Finite (DualSpace p ⧸ L) :=
  Finite.of_surjective L.mkQ L.mkQ_surjective

instance (L : Submodule (ZMod p) (DualSpace p)) : Fintype (PlaneIndex p L) := Fintype.ofFinite _

def planeOf (L : Submodule (ZMod p) (DualSpace p)) (a : PlaneIndex p L) :
    Submodule (ZMod p) (DualSpace p) := a.submodule.comap L.mkQ

theorem line_le_planeOf (L : Submodule (ZMod p) (DualSpace p)) (a : PlaneIndex p L) :
    L ≤ planeOf p L a := Submodule.le_comap_mkQ L a.submodule

theorem planeOf_finrank (L : Submodule (ZMod p) (DualSpace p)) (hL : finrank (ZMod p) L = 2)
    (a : PlaneIndex p L) : finrank (ZMod p) (planeOf p L a) = 3 := by
  let T := planeOf p L a
  let f := L.mkQ.domRestrict T
  have hrange : LinearMap.range f = a.submodule := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_comap_eq_of_surjective L.mkQ_surjective _
  have hker : LinearMap.ker f = L.comap T.subtype := by
    ext x
    change L.mkQ x.val = 0 ↔ x.val ∈ L
    exact Submodule.Quotient.mk_eq_zero L
  have hkd : finrank (ZMod p) (LinearMap.ker f) = 2 := by
    rw [hker, (Submodule.comapSubtypeEquivOfLe (line_le_planeOf p L a)).finrank_eq, hL]
  have hdim := LinearMap.finrank_range_add_finrank_ker (K := ZMod p)
    (V := T) (V₂ := DualSpace p ⧸ L) f
  rw [hrange, a.finrank_submodule, hkd] at hdim
  exact hdim.symm

theorem planeIndex_card (L : Submodule (ZMod p) (DualSpace p)) (hL : finrank (ZMod p) L = 2) :
    Fintype.card (PlaneIndex p L) = p + 1 := by
  have hv : finrank (ZMod p) (DualSpace p) = 4 := by
    simp [DualSpace, ProjectiveGeometry.Vector, Subspace.dual_finrank_eq]
  have hd := L.finrank_quotient_add_finrank
  have hq : finrank (ZMod p) (DualSpace p ⧸ L) = 2 := by rw [hL, hv] at hd; omega
  rw [Fintype.card_eq_nat_card]
  exact (Projectivization.card_of_finrank_two (ZMod p) (DualSpace p ⧸ L) hq).trans
    (by simp [Nat.card_eq_fintype_card])

theorem outside_point_on_planeOf (L : Submodule (ZMod p) (DualSpace p))
    (P : DualPoint p) (hP : P ∉ linePoints p L) :
    ∃ a : PlaneIndex p L, P ∈ linePoints p (planeOf p L a) := by
  have hq : L.mkQ P.rep ≠ 0 := by
    intro hz
    apply hP
    apply (mem_linePoints p L P).mpr
    apply (ProjectiveIncidence.submodule_le_iff_rep_mem P L).mpr
    exact (Submodule.Quotient.mk_eq_zero L).mp hz
  let a := Projectivization.mk (ZMod p) (L.mkQ P.rep) hq
  refine ⟨a, (mem_linePoints p _ P).mpr ?_⟩
  apply (ProjectiveIncidence.submodule_le_iff_rep_mem P _).mpr
  change L.mkQ P.rep ∈ a.submodule
  rw [Projectivization.submodule_mk]
  exact Submodule.mem_span_singleton_self _

def outsideOnPlane (E : Finset (DualPoint p)) (L : Submodule (ZMod p) (DualSpace p))
    (a : PlaneIndex p L) : Finset (DualPoint p) :=
  (E ∩ linePoints p (planeOf p L a)) \ linePoints p L

theorem outsideOnPlane_card_le_two (E : Finset (DualPoint p))
    (L : Submodule (ZMod p) (DualSpace p)) (hL : finrank (ZMod p) L = 2)
    (hline : (E ∩ linePoints p L).card = 2)
    (hplanes : ∀ T : Submodule (ZMod p) (DualSpace p), finrank (ZMod p) T = 3 → L ≤ T →
      (E ∩ linePoints p T).card ≤ 4) (a : PlaneIndex p L) :
    (outsideOnPlane p E L a).card ≤ 2 := by
  have hInt : (E ∩ linePoints p (planeOf p L a)) ∩ linePoints p L = E ∩ linePoints p L := by
    ext P
    simp only [Finset.mem_inter, mem_linePoints]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans (line_le_planeOf p L a)⟩, h.2⟩
  have hcard : ((E ∩ linePoints p (planeOf p L a)) \ linePoints p L).card =
      (E ∩ linePoints p (planeOf p L a)).card - 2 := by
    rw [Finset.card_sdiff, Finset.inter_comm (linePoints p L), hInt, hline]
  have hcap := hplanes (planeOf p L a) (planeOf_finrank p L hL a) (line_le_planeOf p L a)
  change ((E ∩ linePoints p (planeOf p L a)) \ linePoints p L).card ≤ 2
  omega

theorem card_le_two_prime_add_four (E : Finset (DualPoint p))
    (L : Submodule (ZMod p) (DualSpace p)) (hL : finrank (ZMod p) L = 2)
    (hline : (E ∩ linePoints p L).card = 2)
    (hplanes : ∀ T : Submodule (ZMod p) (DualSpace p), finrank (ZMod p) T = 3 → L ≤ T →
      (E ∩ linePoints p T).card ≤ 4) : E.card ≤ 2 * p + 4 := by
  have hcover : E \ linePoints p L ⊆ Finset.univ.biUnion (outsideOnPlane p E L) := by
    intro P hP
    obtain ⟨a, ha⟩ := outside_point_on_planeOf p L P (Finset.mem_sdiff.mp hP).2
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hP).1, ha⟩,
      (Finset.mem_sdiff.mp hP).2⟩
  have hout : (E \ linePoints p L).card ≤ 2 * (p + 1) := by
    calc
      _ ≤ (Finset.univ.biUnion (outsideOnPlane p E L)).card := Finset.card_le_card hcover
      _ ≤ ∑ a : PlaneIndex p L, (outsideOnPlane p E L a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : PlaneIndex p L, (2 : ℕ) := Finset.sum_le_sum
        (fun a _ => outsideOnPlane_card_le_two p E L hL hline hplanes a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, planeIndex_card p L hL,
        Nat.nsmul_eq_mul]; omega
  have hsplit := Finset.card_sdiff_add_card_inter E (linePoints p L)
  rw [hline] at hsplit
  omega

end Cylinder.WhiteLinePlaneCounting

end
