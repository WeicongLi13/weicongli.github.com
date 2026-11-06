module

public import Cylinder.PencilBalance
public import Cylinder.ProjectiveBalance
public import Cylinder.EmptyPlaneChart

/-!
# The balance identity on actual dual projective lines

A line is the set of one-dimensional subspaces of a two-dimensional
dual vector subspace. A line containing an empty plane can be recharted
so that this plane is infinity, where its intersection sum is the
parallel-pencil partition sum. The black and white weights then follow
from the actual intersection quotients.
-/

@[expose] public section

noncomputable section

namespace Cylinder.DualLineBalance

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveChart Cylinder.ProjectiveBalance Cylinder.DualPencils
open scoped BigOperators Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

abbrev DualSpace := Module.Dual (ZMod p) (ProjectiveGeometry.Vector p)

def linePoints (W : Submodule (ZMod p) (DualSpace p)) : Finset (DualPoint p) :=
  Finset.univ.filter (fun H => H.submodule ≤ W)

@[simp] theorem mem_linePoints (W : Submodule (ZMod p) (DualSpace p)) (H : DualPoint p) :
    H ∈ linePoints p W ↔ H.submodule ≤ W := by
  simp [linePoints]

theorem linePoints_card (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2) : (linePoints p W).card = p + 1 := by
  have hcard : Nat.card {H : DualPoint p // H.submodule ≤ W} = p + 1 := by
    rw [← Nat.card_congr (ProjectiveIncidence.projectivizationSubmoduleEquiv W)]
    exact (Projectivization.card_of_finrank_two (ZMod p) W hW).trans
      (by simp [Nat.card_eq_fintype_card])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, linePoints] using hcard

theorem normal_zero_eq_infinity {H : DualPoint p} (hn : ProjectivePointSet.normal p H = 0) :
    H = infinity p := by
  have hall : ∀ i : Fin 3, H.rep (Pi.single i.succ 1) = 0 := by
    intro i
    exact congrFun hn i
  have hform : H.rep = constantTerm p H • infinityFunctional p := by
    apply LinearMap.ext
    intro x
    rw [functional_expansion]
    simp [ProjectiveGeometry.pairing, Fin.sum_univ_succ, hall, constantTerm,
      infinityFunctional, smul_eq_mul]
  rw [← Projectivization.mk_rep H]
  exact (Projectivization.mk_eq_mk_iff' (ZMod p) H.rep (infinityFunctional p)
    H.rep_nonzero (infinityFunctional_ne_zero p)).mpr ⟨constantTerm p H, hform.symm⟩

theorem affinePlaneDual_of_ne_infinity {H : DualPoint p} (hH : H ≠ infinity p) :
    ∃ n : Geometry.Point p, ∃ b : ZMod p, ∃ hn : n ≠ 0,
      H = affinePlaneDual p n b hn := by
  have hn : ProjectivePointSet.normal p H ≠ 0 := by
    intro hz
    exact hH (normal_zero_eq_infinity p hz)
  have hform : affinePlaneFunctional p (ProjectivePointSet.normal p H)
      (-constantTerm p H) = H.rep := by
    apply LinearMap.ext
    intro x
    rw [functional_expansion p H.rep x]
    simp [affinePlaneFunctional, pairingMap, ProjectiveGeometry.pairing,
      Fin.sum_univ_succ, ProjectivePointSet.normal, constantTerm]
  refine ⟨ProjectivePointSet.normal p H, -constantTerm p H, hn, ?_⟩
  calc
    H = Projectivization.mk (ZMod p) H.rep H.rep_nonzero := (Projectivization.mk_rep H).symm
    _ = affinePlaneDual p (ProjectivePointSet.normal p H) (-constantTerm p H) hn :=
      (Projectivization.mk_eq_mk_iff' (ZMod p) H.rep
        (affinePlaneFunctional p (ProjectivePointSet.normal p H) (-constantTerm p H))
        H.rep_nonzero (affinePlaneFunctional_ne_zero p hn _)).mpr ⟨1, by simpa using hform⟩

theorem exists_non_infinity_on_line (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2) :
    ∃ H ∈ linePoints p W, H ≠ infinity p := by
  by_contra h
  have hsub : linePoints p W ⊆ {infinity p} := by
    intro H hH
    apply Finset.mem_singleton.mpr
    by_contra hne
    exact h ⟨H, hH, hne⟩
  have hc := Finset.card_le_card hsub
  rw [linePoints_card p W hW, Finset.card_singleton] at hc
  have hp := (Fact.out : p.Prime).pos
  omega

theorem sum_line_intersection_of_infinity (S : Finset (Geometry.Point p))
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (hinfinity : (infinity p).submodule ≤ W) :
    (∑ H ∈ linePoints p W, (intersection p S H).card) = S.card := by
  obtain ⟨H, hH, hne⟩ := exists_non_infinity_on_line p W hW
  obtain ⟨n, b, hn, hplane⟩ := affinePlaneDual_of_ne_infinity p hne
  have hspan : pencilSubspace p n b = W :=
    pencilSubspace_eq_of_finrank_two p hn b W hW hinfinity (by
      rw [← hplane]
      exact (mem_linePoints p W H).mp hH)
  rw [← hspan]
  calc
    (∑ H ∈ linePoints p (pencilSubspace p n b), (intersection p S H).card) =
        ∑ H : PencilPoint p n b, (intersection p S H.val).card :=
      Finset.sum_subtype _ (fun _ => mem_linePoints p _ _) _
    _ = S.card := PencilBalance.sum_pencil_intersection p S hn b

theorem submodule_mapDual
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p) (H : DualPoint p) :
    (mapDual p e H).submodule = H.submodule.map e.symm.dualMap.toLinearMap := by
  induction H using Projectivization.ind with
  | h f hf =>
    simp only [mapDual, Projectivization.map_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]

theorem mem_mapped_line
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)
    (W : Submodule (ZMod p) (DualSpace p)) (H : DualPoint p) :
    mapDual p e H ∈ linePoints p (W.map e.symm.dualMap.toLinearMap) ↔ H ∈ linePoints p W := by
  rw [mem_linePoints, mem_linePoints, submodule_mapDual,
    Submodule.map_le_map_iff_of_injective e.symm.dualMap.injective]

theorem linePoints_map
    (e : ProjectiveGeometry.Vector p ≃ₗ[ZMod p] ProjectiveGeometry.Vector p)
    (W : Submodule (ZMod p) (DualSpace p)) :
    (linePoints p W).image (mapDual p e) = linePoints p (W.map e.symm.dualMap.toLinearMap) := by
  ext H'
  constructor
  · intro hH'
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hH'
    exact (mem_mapped_line p e W H).mpr hH
  · intro hH'
    obtain ⟨H, rfl⟩ := mapDual_surjective p e H'
    exact Finset.mem_image.mpr ⟨H, (mem_mapped_line p e W H).mp hH', rfl⟩

theorem sum_line_intersection_of_empty (S : Finset (Geometry.Point p))
    (W : Submodule (ZMod p) (DualSpace p)) (hW : Module.finrank (ZMod p) W = 2)
    (H0 : DualPoint p) (hH0 : H0 ∈ linePoints p W) (hempty : intersection p S H0 = ∅) :
    (∑ H ∈ linePoints p W, (intersection p S H).card) = S.card := by
  obtain ⟨e, havoid, hinf, hcard, _hdiv, _hcy, hplanes⟩ :=
    EmptyPlaneChart.empty_plane_as_infinity p S H0 hempty
  let W' := W.map e.symm.dualMap.toLinearMap
  have hW' : Module.finrank (ZMod p) W' = 2 :=
    (LinearEquiv.finrank_map_eq e.symm.dualMap W).trans hW
  have hinfinity : (infinity p).submodule ≤ W' := by
    rw [← hinf, submodule_mapDual]
    exact Submodule.map_mono ((mem_linePoints p W H0).mp hH0)
  calc
    (∑ H ∈ linePoints p W, (intersection p S H).card) =
        ∑ H ∈ linePoints p W,
          (intersection p (S.image (chartMap p e)) (mapDual p e H)).card := by
      apply Finset.sum_congr rfl
      intro H _hH
      exact (hplanes H).symm
    _ = ∑ H ∈ linePoints p W', (intersection p (S.image (chartMap p e)) H).card := by
      rw [← linePoints_map p e W, Finset.sum_image]
      intro H _hH K _hK heq
      exact mapDual_injective p e heq
    _ = (S.image (chartMap p e)).card :=
      sum_line_intersection_of_infinity p _ W' hW' hinfinity
    _ = S.card := hcard

theorem empty_of_white {S : Finset (Geometry.Point p)} (hS : Geometry.PDivisible p S)
    {H : DualPoint p} (hH : H ∈ whitePoints p S) : intersection p S H = ∅ := by
  have hq : quotient p S H = 0 := (Finset.mem_filter.mp hH).2
  apply Finset.card_eq_zero.mp
  rw [← p_mul_quotient p hS H, hq, mul_zero]

theorem sum_line_intersection_of_white {S : Finset (Geometry.Point p)}
    (hS : Geometry.PDivisible p S) (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2)
    (hwhite : (linePoints p W ∩ whitePoints p S).Nonempty) :
    (∑ H ∈ linePoints p W, (intersection p S H).card) = S.card := by
  obtain ⟨H0, hH0⟩ := hwhite
  obtain ⟨hline, hwhite⟩ := Finset.mem_inter.mp hH0
  exact sum_line_intersection_of_empty p S W hW H0 hline (empty_of_white p hS hwhite)

theorem sum_line_quotient_of_white {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2)
    (hwhite : (linePoints p W ∩ whitePoints p S).Nonempty) :
    (∑ H ∈ linePoints p W, quotient p S H) = p := by
  apply Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos
  rw [Finset.mul_sum]
  simp_rw [p_mul_quotient p hS]
  rw [sum_line_intersection_of_white p hS W hW hwhite, hcard]
  ring

theorem white_filter_eq_inter (S : Finset (Geometry.Point p))
    (W : Submodule (ZMod p) (DualSpace p)) :
    WhiteBlackWeights.white (linePoints p W) (quotient p S) = linePoints p W ∩ whitePoints p S := by
  ext H
  simp only [WhiteBlackWeights.white, whitePoints, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, true_and]

theorem black_filter_eq_inter (S : Finset (Geometry.Point p))
    (W : Submodule (ZMod p) (DualSpace p)) :
    WhiteBlackWeights.black (linePoints p W) (quotient p S) = linePoints p W ∩ blackPoints p S := by
  ext H
  simp only [WhiteBlackWeights.black, blackPoints, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, true_and]

/-- The line assertion in the manuscript's balance lemma. -/
theorem line_balance {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (W : Submodule (ZMod p) (DualSpace p))
    (hW : Module.finrank (ZMod p) W = 2)
    (hwhite : (linePoints p W ∩ whitePoints p S).Nonempty) :
    (∑ H ∈ linePoints p W ∩ blackPoints p S, ProjectiveBalance.weight p S H) =
      (linePoints p W ∩ whitePoints p S).card - 1 := by
  have htotal : (∑ H ∈ linePoints p W, quotient p S H) + 1 = (linePoints p W).card := by
    rw [sum_line_quotient_of_white p hcard hS W hW hwhite, linePoints_card p W hW]
  have h := WhiteBlackWeights.sum_black_weight_eq_white_sub_one
    (linePoints p W) (quotient p S) htotal
  simpa only [black_filter_eq_inter, white_filter_eq_inter, ProjectiveBalance.weight,
    WhiteBlackWeights.weight] using h

end Cylinder.DualLineBalance

end
