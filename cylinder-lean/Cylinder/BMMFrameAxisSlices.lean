module

public import Cylinder.BMMClassificationCounting
public import Cylinder.BMMPrimeFourTupleCoordinates
public import Cylinder.BMMCoordinateFibers

/-! The two coordinate axes of the actual black frame are the original
projective cross lines. Their black slices, not only their cardinalities,
are identified, and each slice has between three and four points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMFrameAxisSlices
open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMFourTupleFrame Cylinder.BMMCoordinateFibers Cylinder.ProjectiveSecantCounting
open Cylinder.BMMClassificationCounting Cylinder.BMMBlackLineCapFour
open Cylinder.BMMPrimeFourTupleCoordinates

variable {K : Type*} [Field K]

theorem first_row_proportional (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    ∃ u : K, u ≠ 0 ∧ coordinateRow (blackFrame N T hcap) 1 =
      u • cross R.val.rep (firstCross N T).val.rep := by
  apply annihilator_proportional _ _ _ (coordinateRow_nonzero _ 1) (first_line_coefficients_nonzero N T)
  · rw [coordinateRow_apply, blackFrame_base]
    rfl
  · rw [coordinateRow_apply, blackFrame_first]
    change xScale N T hcap * 0 = 0
    exact mul_zero _

theorem second_row_proportional (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    ∃ u : K, u ≠ 0 ∧ coordinateRow (blackFrame N T hcap) 0 =
      u • cross R.val.rep (thirdCross N T).val.rep := by
  apply annihilator_proportional _ _ _ (coordinateRow_nonzero _ 0) (second_line_coefficients_nonzero N T)
  · rw [coordinateRow_apply, blackFrame_base]
    rfl
  · rw [coordinateRow_apply, blackFrame_third]
    change yScale N T hcap * 0 = 0
    exact mul_zero _

theorem first_axis_incident_iff (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) (P : PlanePoint K) :
    Incident (firstLine N T) P ↔ blackFrame N T hcap P.rep 1 = 0 := by
  obtain ⟨u, hu, hrow⟩ := first_row_proportional N T hcap
  have he : blackFrame N T hcap P.rep 1 = u * dot (cross R.val.rep (firstCross N T).val.rep) P.rep := by
    rw [← coordinateRow_apply, hrow, dot_smul_coefficients]
  change Incident (Projectivization.mk K _ (first_line_coefficients_nonzero N T)) P ↔ _
  rw [incident_mk_iff, he, mul_eq_zero]
  exact (or_iff_right hu).symm

theorem second_axis_incident_iff (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) (P : PlanePoint K) :
    Incident (secondLine N T) P ↔ blackFrame N T hcap P.rep 0 = 0 := by
  obtain ⟨u, hu, hrow⟩ := second_row_proportional N T hcap
  have he : blackFrame N T hcap P.rep 0 = u * dot (cross R.val.rep (thirdCross N T).val.rep) P.rep := by
    rw [← coordinateRow_apply, hrow, dot_smul_coefficients]
  change Incident (Projectivization.mk K _ (second_line_coefficients_nonzero N T)) P ↔ _
  rw [incident_mk_iff, he, mul_eq_zero]
  exact (or_iff_right hu).symm

theorem first_axis_points (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    (coordinateBlacks N (blackFrame N T hcap) 1).image (fun P : N.B => P.val) =
      lineSlice N.B (firstLine N T) := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_filter.mpr ⟨Q.property,
      (first_axis_incident_iff N T hcap Q.val).mpr (Finset.mem_filter.mp hQ).2⟩
  · intro hP
    obtain ⟨hPB, hinc⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_image.mpr ⟨⟨P, hPB⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (first_axis_incident_iff N T hcap P).mp hinc⟩, rfl⟩

theorem second_axis_points (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    (coordinateBlacks N (blackFrame N T hcap) 0).image (fun P : N.B => P.val) =
      lineSlice N.B (secondLine N T) := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_filter.mpr ⟨Q.property,
      (second_axis_incident_iff N T hcap Q.val).mpr (Finset.mem_filter.mp hQ).2⟩
  · intro hP
    obtain ⟨hPB, hinc⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_image.mpr ⟨⟨P, hPB⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (second_axis_incident_iff N T hcap P).mp hinc⟩, rfl⟩

theorem first_axis_card (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    (lineSlice N.B (firstLine N T)).card = (coordinateBlacks N (blackFrame N T hcap) 1).card := by
  rw [← first_axis_points N T hcap, Finset.card_image_of_injective _ Subtype.val_injective]

theorem second_axis_card (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    (lineSlice N.B (secondLine N T)).card = (coordinateBlacks N (blackFrame N T hcap) 0).card := by
  rw [← second_axis_points N T hcap, Finset.card_image_of_injective _ Subtype.val_injective]

theorem first_axis_card_bounds (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    3 ≤ (lineSlice N.B (firstLine N T)).card ∧ (lineSlice N.B (firstLine N T)).card ≤ 4 := by
  have hne : R ≠ firstCross N T ∧ R ≠ secondCross N T ∧ firstCross N T ≠ secondCross N T :=
    ⟨base_ne_first N T, base_ne_second N T, opposite_secants_ne N T⟩
  have hcard : ({R, firstCross N T, secondCross N T} : Finset N.B).card = 3 := by simp [hne.1, hne.2.1, hne.2.2]
  have hsub : ({R, firstCross N T, secondCross N T} : Finset N.B) ⊆
      coordinateBlacks N (blackFrame N T hcap) 1 := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hP with rfl | rfl | rfl
    · rw [blackFrame_base]
      rfl
    · rw [blackFrame_first]
      change xScale N T hcap * 0 = 0
      exact mul_zero _
    · rw [blackFrame_second]
      change baseFrame N T hcap (secondCross N T).val.rep 2 * 0 = 0
      exact mul_zero _
  constructor
  · rw [first_axis_card N T hcap]
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    exact hc
  · exact hcap (firstLine N T).rep (firstLine N T).rep_nonzero

theorem second_axis_card_bounds (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    3 ≤ (lineSlice N.B (secondLine N T)).card ∧ (lineSlice N.B (secondLine N T)).card ≤ 4 := by
  have hne : R ≠ thirdCross N T ∧ R ≠ fourthCross N T ∧ thirdCross N T ≠ fourthCross N T :=
    ⟨base_ne_third N T, base_ne_fourth N T, other_opposite_secants_ne N T⟩
  have hcard : ({R, thirdCross N T, fourthCross N T} : Finset N.B).card = 3 := by simp [hne.1, hne.2.1, hne.2.2]
  have hsub : ({R, thirdCross N T, fourthCross N T} : Finset N.B) ⊆
      coordinateBlacks N (blackFrame N T hcap) 0 := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hP with rfl | rfl | rfl
    · rw [blackFrame_base]
      rfl
    · rw [blackFrame_third]
      change yScale N T hcap * 0 = 0
      exact mul_zero _
    · rw [blackFrame_fourth]
      change baseFrame N T hcap (fourthCross N T).val.rep 2 * 0 = 0
      exact mul_zero _
  constructor
  · rw [second_axis_card N T hcap]
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    exact hc
  · exact hcap (secondLine N T).rep (secondLine N T).rep_nonzero

theorem coordinate_axes_card_bounds (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (hcap : LineCap N.B 4) :
    (3 ≤ (coordinateBlacks N (blackFrame N T hcap) 1).card ∧
      (coordinateBlacks N (blackFrame N T hcap) 1).card ≤ 4) ∧
    (3 ≤ (coordinateBlacks N (blackFrame N T hcap) 0).card ∧
      (coordinateBlacks N (blackFrame N T hcap) 0).card ≤ 4) := by
  rw [← first_axis_card N T hcap, ← second_axis_card N T hcap]
  exact ⟨first_axis_card_bounds N T hcap, second_axis_card_bounds N T hcap⟩

theorem prime_axes_card_bounds (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) {R : N.B} (T : FourTuple (configuration N) N.E R) :
    (3 ≤ (coordinateBlacks N (primeBlackFrame p hp N T) 1).card ∧
      (coordinateBlacks N (primeBlackFrame p hp N T) 1).card ≤ 4) ∧
    (3 ≤ (coordinateBlacks N (primeBlackFrame p hp N T) 0).card ∧
      (coordinateBlacks N (primeBlackFrame p hp N T) 0).card ≤ 4) :=
  coordinate_axes_card_bounds N T (normalized_black_line_cap_four p hp N)

end Cylinder.BMMFrameAxisSlices
end
