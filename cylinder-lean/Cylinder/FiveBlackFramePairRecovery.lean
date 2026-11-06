module

public import Cylinder.FiveBlackFrameRecovery
public import Cylinder.BMMFourTupleBlackGeometry

/-! Actual black pair sets in two frames determine the same unordered
white pair family. The only coordinate inputs are the true black frame
identities and the four homogeneous diagonal equations. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FiveBlackFramePairRecovery

open Cylinder.RationalPlaneLine Cylinder.BMMLinearCoordinates Cylinder.FiveBlackFrameRecovery
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry

variable {K : Type*} [Field K]

theorem linearPointMap_transition (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint K) :
    linearPointMap (g.symm.trans g') (linearPointMap g P) = linearPointMap g' P := by
  rw [linearPointMap_rep g P, linearPointMap_mk, linearPointMap_rep g' P]
  congr 1
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem pointSet_transition (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (C : Finset (PlanePoint K)) :
    (C.image (linearPointMap g)).image (linearPointMap (g.symm.trans g')) = C.image (linearPointMap g') := by
  rw [Finset.image_image]
  exact Finset.image_congr (fun P _hP => linearPointMap_transition g g' P)

theorem diagonal_family_eq_of_black_sets (W : Finset (PlanePoint K)) (R : PlanePoint K)
    (C D : Finset (PlanePoint K)) (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hR : g R.rep = vertex) (hR' : g' R.rep = vertex)
    (hC : C.image (linearPointMap g) = {axisPoint 0, axisShiftPoint 0})
    (hC' : C.image (linearPointMap g') = {axisPoint 0, axisShiftPoint 0})
    (hD : D.image (linearPointMap g) = {axisPoint 1, axisShiftPoint 1})
    (hD' : D.image (linearPointMap g') = {axisPoint 1, axisShiftPoint 1}) :
    ({positiveSlice W g', negativeSlice W g'} : Finset (Finset (PlanePoint K))) =
      {positiveSlice W g, negativeSlice W g} := by
  apply diagonal_slice_family_eq W g g'
  · calc
      (g.symm.trans g') vertex = (g.symm.trans g') (g R.rep) := congrArg (g.symm.trans g') hR.symm
      _ = g' R.rep := by simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      _ = vertex := hR'
  · intro i
    fin_cases i
    · have hh := pointSet_transition g g' C
      rwa [hC, hC'] at hh
    · have hh := pointSet_transition g g' D
      rwa [hD, hD'] at hh

theorem normalized_diagonal_iff (N : NormalizedSystem K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : N.W) (a : K) :
    (g (N.E P) 0 = a * g (N.E P) 1) ↔ (g P.val.rep 0 = a * g P.val.rep 1) := by
  obtain ⟨c, hc, hrep⟩ := N.representatives P
  rw [hrep, map_smul]
  change (c * g P.val.rep 0 = a * (c * g P.val.rep 1)) ↔
    (g P.val.rep 0 = a * g P.val.rep 1)
  constructor
  · intro h
    apply mul_left_cancel₀ hc
    calc
      c * g P.val.rep 0 = a * (c * g P.val.rep 1) := h
      _ = c * (a * g P.val.rep 1) := by ring
  · intro h
    rw [h]
    ring

def pairKey (N : NormalizedSystem K) {R : N.B} (T : FourTuple (configuration N) N.E R) :
    Finset (Finset (PlanePoint K)) := {{T.P.val, T.Q.val}, {T.U.val, T.V.val}}

theorem white_pair_slices (N : NormalizedSystem K) {R : N.B}
    (T : FourTuple (configuration N) N.E R) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hP : g (N.E T.P) 0 = g (N.E T.P) 1)
    (hQ : g (N.E T.Q) 0 = g (N.E T.Q) 1)
    (hU : g (N.E T.U) 0 = -(g (N.E T.U) 1))
    (hV : g (N.E T.V) 0 = -(g (N.E T.V) 1)) :
    positiveSlice N.W g = {T.P.val, T.Q.val} ∧ negativeSlice N.W g = {T.U.val, T.V.val} := by
  have hPc : g T.P.val.rep 0 = (1 : K) * g T.P.val.rep 1 :=
    (normalized_diagonal_iff N g T.P 1).mp (by simpa only [one_mul] using hP)
  have hQc : g T.Q.val.rep 0 = (1 : K) * g T.Q.val.rep 1 :=
    (normalized_diagonal_iff N g T.Q 1).mp (by simpa only [one_mul] using hQ)
  have hUc : g T.U.val.rep 0 = (-1 : K) * g T.U.val.rep 1 :=
    (normalized_diagonal_iff N g T.U (-1)).mp (by simpa only [neg_one_mul] using hU)
  have hVc : g T.V.val.rep 0 = (-1 : K) * g T.V.val.rep 1 :=
    (normalized_diagonal_iff N g T.V (-1)).mp (by simpa only [neg_one_mul] using hV)
  have hmap (v : Fin 3 → K) : ProjectiveFieldEmbedding.vectorMap (RingHom.id K) v = v := rfl
  constructor
  · have hh := ArcCoordinateRecovery.diagonal_slice_eq_pair N.W N.arc (RingHom.id K) g 1
      T.P.val T.Q.val T.P.property T.Q.property (fun h => T.hPQ (Subtype.ext h)) hPc hQc
    have heq : positiveSlice N.W g = ArcCoordinateRecovery.diagonalSlice N.W (RingHom.id K) g 1 := by
      ext P
      simp only [positiveSlice, ArcCoordinateRecovery.diagonalSlice, Finset.mem_filter]
      rw [hmap, one_mul]
    exact heq.trans hh
  · have hh := ArcCoordinateRecovery.diagonal_slice_eq_pair N.W N.arc (RingHom.id K) g (-1)
      T.U.val T.V.val T.U.property T.V.property (fun h => T.hUV (Subtype.ext h)) hUc hVc
    have heq : negativeSlice N.W g = ArcCoordinateRecovery.diagonalSlice N.W (RingHom.id K) g (-1) := by
      ext P
      simp only [negativeSlice, ArcCoordinateRecovery.diagonalSlice, Finset.mem_filter]
      rw [hmap, neg_one_mul]
    exact heq.trans hh

theorem pair_key_recovered_from_black_sets (N : NormalizedSystem K) {R : N.B}
    (T T' : FourTuple (configuration N) N.E R) (C D : Finset (PlanePoint K))
    (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hR : g R.val.rep = vertex) (hR' : g' R.val.rep = vertex)
    (hC : C.image (linearPointMap g) = {axisPoint 0, axisShiftPoint 0})
    (hC' : C.image (linearPointMap g') = {axisPoint 0, axisShiftPoint 0})
    (hD : D.image (linearPointMap g) = {axisPoint 1, axisShiftPoint 1})
    (hD' : D.image (linearPointMap g') = {axisPoint 1, axisShiftPoint 1})
    (hP : g (N.E T.P) 0 = g (N.E T.P) 1)
    (hQ : g (N.E T.Q) 0 = g (N.E T.Q) 1)
    (hU : g (N.E T.U) 0 = -(g (N.E T.U) 1))
    (hV : g (N.E T.V) 0 = -(g (N.E T.V) 1))
    (hP' : g' (N.E T'.P) 0 = g' (N.E T'.P) 1)
    (hQ' : g' (N.E T'.Q) 0 = g' (N.E T'.Q) 1)
    (hU' : g' (N.E T'.U) 0 = -(g' (N.E T'.U) 1))
    (hV' : g' (N.E T'.V) 0 = -(g' (N.E T'.V) 1)) : pairKey N T' = pairKey N T := by
  obtain ⟨hpos, hneg⟩ := white_pair_slices N T g hP hQ hU hV
  obtain ⟨hpos', hneg'⟩ := white_pair_slices N T' g' hP' hQ' hU' hV'
  have hh := diagonal_family_eq_of_black_sets N.W R.val C D g g' hR hR' hC hC' hD hD'
  rwa [hpos, hneg, hpos', hneg'] at hh

end Cylinder.FiveBlackFramePairRecovery

end
