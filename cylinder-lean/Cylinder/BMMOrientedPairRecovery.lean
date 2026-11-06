module

public import Cylinder.BMMOrientedAxes
public import Cylinder.BMMFrameAxisSlices
public import Cylinder.BMMFourSecantWhiteCoordinates
public import Cylinder.FiveBlackFramePairRecovery
public import Cylinder.ProjectiveHalfMidpoint
public import Cylinder.ProjectiveLineChartTransition

/-! Two actual nonspecial configurations with the same three- and
four-point black axes have the same literal unordered white-pair key.
The fourth black midpoint is constructed by the actual matchings. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMOrientedPairRecovery

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMFourTupleFrame Cylinder.BMMFourTupleCoordinates Cylinder.BMMCoordinateFibers
open Cylinder.BMMFourSecantWhiteCoordinates Cylinder.BMMFrameAxisSlices
open Cylinder.BMMClassificationCounting Cylinder.ProjectiveSecantCounting Cylinder.BMMOrientedAxes
open Cylinder.BMMThreeSecantConfigurations Cylinder.BMMLinearCoordinates Cylinder.FiveBlackFrameRecovery
open Cylinder.FiveBlackFramePairRecovery Cylinder.ProjectiveHalfMidpoint Cylinder.ProjectiveLineChartTransition

variable {K : Type*} [Field K]

theorem image_point_of_scaled_rep (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint K)
    (v : Fin 3 → K) (hv : v ≠ 0) (a : K) (h : g P.rep = a • v) :
    linearPointMap g P = Projectivization.mk K v hv := by
  rw [linearPointMap_rep]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a, h.symm⟩

theorem first_black_pair_image (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    ({(firstCross N T).val, (secondCross N T).val} : Finset (PlanePoint K)).image
      (linearPointMap (blackFrame N T hcap)) = {axisPoint 0, axisShiftPoint 0} := by
  rw [Finset.image_insert, Finset.image_singleton]
  have h0 : linearPointMap (blackFrame N T hcap) (firstCross N T).val = axisPoint 0 := by
    apply image_point_of_scaled_rep _ _ _ (axisVector_nonzero 0) (xScale N T hcap)
    exact blackFrame_first N T hcap
  have h1 : linearPointMap (blackFrame N T hcap) (secondCross N T).val = axisShiftPoint 0 := by
    apply image_point_of_scaled_rep _ _ _ (axisShift_nonzero 0)
      (baseFrame N T hcap (secondCross N T).val.rep 2)
    simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using blackFrame_second N T hcap
  rw [h0, h1]

theorem second_black_pair_image (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    ({(thirdCross N T).val, (fourthCross N T).val} : Finset (PlanePoint K)).image
      (linearPointMap (blackFrame N T hcap)) = {axisPoint 1, axisShiftPoint 1} := by
  rw [Finset.image_insert, Finset.image_singleton]
  have h0 : linearPointMap (blackFrame N T hcap) (thirdCross N T).val = axisPoint 1 := by
    apply image_point_of_scaled_rep _ _ _ (axisVector_nonzero 1) (yScale N T hcap)
    exact blackFrame_third N T hcap
  have h1 : linearPointMap (blackFrame N T hcap) (fourthCross N T).val = axisShiftPoint 1 := by
    apply image_point_of_scaled_rep _ _ _ (axisShift_nonzero 1)
      (baseFrame N T hcap (fourthCross N T).val.rep 2)
    simpa [axisVector, vertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using blackFrame_fourth N T hcap
  rw [h0, h1]

theorem first_black_pair_erase (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4)
    (hthree : (lineSlice N.B (firstLine N T)).card = 3) :
    (lineSlice N.B (firstLine N T)).erase R.val = {(firstCross N T).val, (secondCross N T).val} := by
  have hR : R.val ∈ lineSlice N.B (firstLine N T) :=
    Finset.mem_filter.mpr ⟨R.property, first_axis_incident_base N T⟩
  have h1 : (firstCross N T).val ∈ lineSlice N.B (firstLine N T) := by
    apply Finset.mem_filter.mpr
    refine ⟨(firstCross N T).property, (first_axis_incident_iff N T hcap _).mpr ?_⟩
    rw [blackFrame_first]
    change xScale N T hcap * 0 = 0
    exact mul_zero _
  have h2 : (secondCross N T).val ∈ lineSlice N.B (firstLine N T) := by
    apply Finset.mem_filter.mpr
    refine ⟨(secondCross N T).property, (first_axis_incident_iff N T hcap _).mpr ?_⟩
    rw [blackFrame_second]
    change baseFrame N T hcap (secondCross N T).val.rep 2 * 0 = 0
    exact mul_zero _
  have hR1 : (firstCross N T).val ≠ R.val := fun h => base_ne_first N T (Subtype.ext h.symm)
  have hR2 : (secondCross N T).val ≠ R.val := fun h => base_ne_second N T (Subtype.ext h.symm)
  have h12 : (firstCross N T).val ≠ (secondCross N T).val :=
    fun h => opposite_secants_ne N T (Subtype.ext h)
  have hsub : ({(firstCross N T).val, (secondCross N T).val} : Finset (PlanePoint K)) ⊆
      (lineSlice N.B (firstLine N T)).erase R.val := by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact Finset.mem_erase.mpr ⟨hR1, h1⟩
    have hP2 := Finset.mem_singleton.mp hP
    subst P
    exact Finset.mem_erase.mpr ⟨hR2, h2⟩
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_erase_of_mem hR, hthree, Finset.card_pair h12]

theorem half_black_data (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) (htwo : (2 : K) ≠ 0)
    (hfour : (lineSlice N.B (secondLine N T)).card = 4) :
    ∃ D : N.B, D.val ∈ (lineSlice N.B (secondLine N T)).erase R.val ∧
      ((lineSlice N.B (secondLine N T)).erase R.val).erase D.val =
        {(thirdCross N T).val, (fourthCross N T).val} ∧
      (∑ P ∈ ((lineSlice N.B (secondLine N T)).erase R.val).erase D.val,
        LineAffineCoordinates.lineParameter (blackFrame N T hcap) P) =
          2 * LineAffineCoordinates.lineParameter (blackFrame N T hcap) D.val := by
  have hc : (coordinateBlacks N (blackFrame N T hcap) 0).card = 4 := by
    rwa [← second_axis_card N T hcap]
  obtain ⟨D⟩ := x_four_completion_exists N T hcap htwo hc
  obtain ⟨a, c, ha, _hc, _hs, _hca, hP, hQ, hU, hV⟩ := actual_four_white_coordinates N T hcap htwo
  change blackFrame N T hcap (N.E T.P) = _ at hP
  change blackFrame N T hcap (N.E T.Q) = _ at hQ
  change blackFrame N T hcap (N.E T.U) = _ at hU
  change blackFrame N T hcap (N.E T.V) = _ at hV
  obtain ⟨_hX, _hY, k, hk, hD⟩ := four_completion_x_coordinates N T hcap D a c ha htwo hP hQ hU hV
  have hRB : R.val ∈ lineSlice N.B (secondLine N T) :=
    Finset.mem_filter.mpr ⟨R.property, second_axis_incident_base N T⟩
  have h0B : (thirdCross N T).val ∈ lineSlice N.B (secondLine N T) := by
    refine Finset.mem_filter.mpr ⟨(thirdCross N T).property, (second_axis_incident_iff N T hcap _).mpr ?_⟩
    rw [blackFrame_third]
    change yScale N T hcap * 0 = 0
    exact mul_zero _
  have h1B : (fourthCross N T).val ∈ lineSlice N.B (secondLine N T) := by
    refine Finset.mem_filter.mpr ⟨(fourthCross N T).property, (second_axis_incident_iff N T hcap _).mpr ?_⟩
    rw [blackFrame_fourth]
    change baseFrame N T hcap (fourthCross N T).val.rep 2 * 0 = 0
    exact mul_zero _
  have hDB : D.D.val ∈ lineSlice N.B (secondLine N T) := by
    refine Finset.mem_filter.mpr ⟨D.D.property, (second_axis_incident_iff N T hcap _).mpr ?_⟩
    rw [hD]
    change k * 0 = 0
    exact mul_zero _
  exact ⟨D.D, four_point_half_midpoint (blackFrame N T hcap) _ hfour R.val
    (thirdCross N T).val (fourthCross N T).val D.D.val hRB h0B h1B hDB
    (yScale N T hcap) (baseFrame N T hcap (fourthCross N T).val.rep 2) k
    (yScale_nonzero N T hcap) (fourth_coordinates_nonzero N T hcap).2 hk htwo
    (blackFrame_base N T hcap) (blackFrame_third N T hcap) (blackFrame_fourth N T hcap) hD⟩

theorem white_frame_diagonals (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) (htwo : (2 : K) ≠ 0) :
    blackFrame N T hcap (N.E T.P) 0 = blackFrame N T hcap (N.E T.P) 1 ∧
      blackFrame N T hcap (N.E T.Q) 0 = blackFrame N T hcap (N.E T.Q) 1 ∧
      blackFrame N T hcap (N.E T.U) 0 = -(blackFrame N T hcap (N.E T.U) 1) ∧
      blackFrame N T hcap (N.E T.V) 0 = -(blackFrame N T hcap (N.E T.V) 1) := by
  obtain ⟨a, c, _ha, _hc, _hs, _hca, hP, hQ, hU, hV⟩ := actual_four_white_coordinates N T hcap htwo
  change blackFrame N T hcap (N.E T.P) = _ at hP
  change blackFrame N T hcap (N.E T.Q) = _ at hQ
  change blackFrame N T hcap (N.E T.U) = _ at hU
  change blackFrame N T hcap (N.E T.V) = _ at hV
  rw [hP, hQ, hU, hV]
  simp

theorem oriented_pair_key_eq (N : NormalizedSystem K) {R : N.B}
    (T U : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4)
    (htwo : (2 : K) ≠ 0) (hthree : (3 : K) ≠ 0)
    (hfirst : firstLine N T = firstLine N U) (hsecond : secondLine N T = secondLine N U)
    (hfirst3 : (lineSlice N.B (firstLine N T)).card = 3)
    (hsecond4 : (lineSlice N.B (secondLine N T)).card = 4) :
    fourTupleKey N R T = fourTupleKey N R U := by
  have hfirst3U : (lineSlice N.B (firstLine N U)).card = 3 := by rwa [← hfirst]
  have hsecond4U : (lineSlice N.B (secondLine N U)).card = 4 := by rwa [← hsecond]
  have hfirstPair : ({(firstCross N T).val, (secondCross N T).val} : Finset (PlanePoint K)) =
      {(firstCross N U).val, (secondCross N U).val} := by
    rw [← first_black_pair_erase N T hcap hfirst3, hfirst, first_black_pair_erase N U hcap hfirst3U]
  obtain ⟨DT, hDT, hDTpair, hDTmid⟩ := half_black_data N T hcap htwo hsecond4
  obtain ⟨DU, hDU, hDUpair, hDUmid⟩ := half_black_data N U hcap htwo hsecond4U
  rw [← hsecond] at hDU hDUpair hDUmid
  let B := lineSlice N.B (secondLine N T)
  have hRB : R.val ∈ B := Finset.mem_filter.mpr ⟨R.property, second_axis_incident_base N T⟩
  have hlineT : ∀ P ∈ B, blackFrame N T hcap P.rep 0 = 0 :=
    fun P hP => (second_axis_incident_iff N T hcap P).mp (Finset.mem_filter.mp hP).2
  have hlineU : ∀ P ∈ B, blackFrame N U hcap P.rep 0 = 0 := by
    intro P hP
    apply (second_axis_incident_iff N U hcap P).mp
    rw [← hsecond]
    exact (Finset.mem_filter.mp hP).2
  have hRT : blackFrame N T hcap R.val.rep 1 = 0 := by rw [blackFrame_base]; rfl
  have hRU : blackFrame N U hcap R.val.rep 1 = 0 := by rw [blackFrame_base]; rfl
  have hmid := four_point_midpoint_pair_unique_across_charts (blackFrame N T hcap) (blackFrame N U hcap)
    B R.val hRB hsecond4 hlineT hlineU hRT hRU hthree ⟨DT.val, hDT⟩ ⟨DU.val, hDU⟩ hDTmid hDUmid
  have hsecondPair : ({(thirdCross N T).val, (fourthCross N T).val} : Finset (PlanePoint K)) =
      {(thirdCross N U).val, (fourthCross N U).val} := hDTpair.symm.trans (hmid.2.1.trans hDUpair)
  obtain ⟨hP, hQ, hU, hV⟩ := white_frame_diagonals N T hcap htwo
  obtain ⟨hP', hQ', hU', hV'⟩ := white_frame_diagonals N U hcap htwo
  have hkeys := pair_key_recovered_from_black_sets N T U
    {(firstCross N T).val, (secondCross N T).val} {(thirdCross N T).val, (fourthCross N T).val}
    (blackFrame N T hcap) (blackFrame N U hcap) (blackFrame_base N T hcap) (blackFrame_base N U hcap)
    (first_black_pair_image N T hcap) (by rw [hfirstPair]; exact first_black_pair_image N U hcap)
    (second_black_pair_image N T hcap) (by rw [hsecondPair]; exact second_black_pair_image N U hcap)
    hP hQ hU hV hP' hQ' hU' hV'
  exact hkeys.symm

theorem axis_recovery_of_black_cap (N : NormalizedSystem K) (hcap : LineCap N.B 4)
    (htwo : (2 : K) ≠ 0) (hthree : (3 : K) ≠ 0) : AxisRecovery N := by
  intro R ell m hell3 hm4 T U hT hU
  obtain ⟨T', hTfirst, hTsecond, hTkey⟩ := exists_oriented_axes N T ell m hT
  obtain ⟨U', hUfirst, hUsecond, hUkey⟩ := exists_oriented_axes N U ell m hU
  have hkey := oriented_pair_key_eq N T' U' hcap htwo hthree
    (hTfirst.trans hUfirst.symm) (hTsecond.trans hUsecond.symm)
    (by rw [hTfirst]; exact hell3) (by rw [hTsecond]; exact hm4)
  exact hTkey.symm.trans (hkey.trans hUkey)

theorem prime_axis_recovery (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (N : NormalizedSystem (ZMod p)) :
    AxisRecovery N := by
  have hp3 : 3 ≤ p := by omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hdiv
    omega
  exact axis_recovery_of_black_cap N (BMMBlackLineCapFour.normalized_black_line_cap_four p hp3 N)
    (BMMFinitePlaneArcBound.prime_two_nonzero p hp3) hthree

end Cylinder.BMMOrientedPairRecovery

end
