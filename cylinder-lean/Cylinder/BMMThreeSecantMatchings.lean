module

public import Cylinder.BMMCoordinateFibers
public import Cylinder.BMMFourTupleBlackGeometry

/-! Three actual black points on a coordinate line force the two
remaining white points of the corresponding three-by-three matching.
Their existence and all four new secants are derived here. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMThreeSecantMatchings

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlockerPairs
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMCoordinateFibers

variable {K : Type*} [Field K]

theorem partner_ne_of_other_secant (A : NormalizedSystem K) (B C : A.B) (hBC : B ≠ C)
    (P Q : A.W) (hPQ : P ≠ Q) (hcol : Collinear P.val Q.val C.val) : partner A B P ≠ Q := by
  intro heq
  have hc := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card B P).2
  change Collinear P.val (partner A B P).val B.val at hc
  rw [heq] at hc
  have hB := secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ B hc
  have hC := secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ C hcol
  exact hBC (hB.symm.trans hC)

theorem secant_coordinate_flip (A : NormalizedSystem K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) (P Q : A.W) (hPQ : P ≠ Q)
    (hz : g (secant A P Q hPQ).val.rep i = 0) : g (A.E Q) i = -g (A.E P) i := by
  obtain ⟨a, _ha, hs⟩ := A.sums P Q hPQ
  have h := congrArg (fun v : Fin 3 → K => g v i) hs
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  change g (A.E P) i + g (A.E Q) i = a * g (secant A P Q hPQ).val.rep i at h
  rw [hz, mul_zero] at h
  linear_combination h

structure Completion (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) where
  X : A.W
  Y : A.W
  hXP : X ≠ T.P
  hXQ : X ≠ T.Q
  hXU : X ≠ T.U
  hXV : X ≠ T.V
  hYP : Y ≠ T.P
  hYQ : Y ≠ T.Q
  hYU : Y ≠ T.U
  hYV : Y ≠ T.V
  hXY : X ≠ Y
  firstX : Collinear T.Q.val X.val (firstCross A T).val
  secondX : Collinear T.U.val X.val (secondCross A T).val
  firstY : Collinear T.V.val Y.val (firstCross A T).val
  secondY : Collinear T.P.val Y.val (secondCross A T).val

theorem exists_completion (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3)
    (htwo : (2 : K) ≠ 0) (hcard : (coordinateBlacks A g i).card = 3)
    (hR : g R.val.rep i = 0) (hB : g (firstCross A T).val.rep i = 0)
    (hC : g (secondCross A T).val.rep i = 0) : Nonempty (Completion A T) := by
  let B := firstCross A T
  let C := secondCross A T
  let X := partner A B T.Q
  let X' := partner A C T.U
  let Y := partner A B T.V
  let Y' := partner A C T.P
  have hRB : R ≠ B := base_ne_first A T
  have hRC : R ≠ C := base_ne_second A T
  have hBC : B ≠ C := opposite_secants_ne A T
  have hcolB : Collinear T.P.val T.U.val B.val :=
    secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card T.P T.U T.hPU
  have hcolC : Collinear T.Q.val T.V.val C.val :=
    secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.V T.hQV
  have hXP : X ≠ T.P := partner_ne_of_other_secant A B R hRB.symm T.Q T.P T.hPQ.symm
    (collinear_swap _ _ _ T.first_collinear)
  have hXV : X ≠ T.V := partner_ne_of_other_secant A B C hBC T.Q T.V T.hQV hcolC
  have hX'P : X' ≠ T.P := partner_ne_of_other_secant A C B hBC.symm T.U T.P T.hPU.symm
    (collinear_swap _ _ _ hcolB)
  have hX'V : X' ≠ T.V := partner_ne_of_other_secant A C R hRC.symm T.U T.V T.hUV T.second_collinear
  have hYQ : Y ≠ T.Q := partner_ne_of_other_secant A B C hBC T.V T.Q T.hQV.symm
    (collinear_swap _ _ _ hcolC)
  have hYU : Y ≠ T.U := partner_ne_of_other_secant A B R hRB.symm T.V T.U T.hUV.symm
    (collinear_swap _ _ _ T.second_collinear)
  have hY'Q : Y' ≠ T.Q := partner_ne_of_other_secant A C R hRC.symm T.P T.Q T.hPQ T.first_collinear
  have hY'U : Y' ≠ T.U := partner_ne_of_other_secant A C B hBC.symm T.P T.U T.hPU hcolB
  have hbmem : B ∈ coordinateBlacks A g i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
  have hcmem : C ∈ coordinateBlacks A g i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩
  have hQR : g (A.E T.Q) i = -g (A.E T.P) i := by
    apply secant_coordinate_flip A g i T.P T.Q T.hPQ
    have hb := first_blocker (configuration A) A.E R T
    change secant A T.P T.Q T.hPQ = R at hb
    rw [hb]
    exact hR
  have hUP : g (A.E T.U) i = -g (A.E T.P) i := secant_coordinate_flip A g i T.P T.U T.hPU hB
  have hVU : g (A.E T.V) i = -g (A.E T.U) i := by
    apply secant_coordinate_flip A g i T.U T.V T.hUV
    have hb := second_blocker (configuration A) A.E R T
    change secant A T.U T.V T.hUV = R at hb
    rw [hb]
    exact hR
  have hVP : g (A.E T.V) i = g (A.E T.P) i := by rw [hVU, hUP, neg_neg]
  let F := coordinateFiber A g i (g (A.E T.P) i)
  let G := coordinateFiber A g i (-g (A.E T.P) i)
  have hF : F.card = 3 := (coordinateFiber_card A g i htwo (by omega) T.P).trans hcard
  have hG : G.card = 3 := (negative_coordinateFiber_card A g i htwo (by omega) T.P).trans hcard
  have hpF : T.P ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hvF : T.V ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hVP⟩
  have hqG : T.Q ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQR⟩
  have huG : T.U ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUP⟩
  have hXF : X ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := partner_coordinate_flip A g i B hbmem T.Q
    simpa only [hQR, neg_neg] using h
  have hX'F : X' ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := partner_coordinate_flip A g i C hcmem T.U
    simpa only [hUP, neg_neg] using h
  have hYG : Y ∈ G := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hVP] using partner_coordinate_flip A g i B hbmem T.V
  have hY'G : Y' ∈ G := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, partner_coordinate_flip A g i C hcmem T.P⟩
  have hXX' : X = X' := unique_third_of_card_three F hF T.P T.V X X' hpF hvF T.hPV
    hXF hXP hXV hX'F hX'P hX'V
  have hYY' : Y = Y' := unique_third_of_card_three G hG T.Q T.U Y Y' hqG huG T.hQU
    hYG hYQ hYU hY'G hY'Q hY'U
  have hXU : X ≠ T.U := by
    rw [hXX']
    exact blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card C T.U
  have hYP : Y ≠ T.P := by
    rw [hYY']
    exact blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card C T.P
  refine ⟨{
    X := X, Y := Y, hXP := hXP,
    hXQ := blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card B T.Q,
    hXU := hXU, hXV := hXV, hYP := hYP, hYQ := hYQ, hYU := hYU,
    hYV := blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card B T.V,
    hXY := fun h => T.hQV ((blackPartner_involutive A.W A.B A.arc A.disjoint A.blocks A.card B).injective h),
    firstX := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card B T.Q).2,
    secondX := ?_,
    firstY := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card B T.V).2,
    secondY := ?_ }⟩
  · rw [hXX']
    exact (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card C T.U).2
  · rw [hYY']
    exact (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card C T.P).2

end Cylinder.BMMThreeSecantMatchings

end
