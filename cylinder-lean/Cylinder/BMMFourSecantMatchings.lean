module

public import Cylinder.FourByFourMatching
public import Cylinder.BMMThreeSecantMatchings

/-! Four actual black points and their bijective white matchings give
the required four-secant entries without assuming the matching table. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMFourSecantMatchings

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlockerPairs
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry
open Cylinder.BMMCoordinateFibers Cylinder.BMMThreeSecantMatchings Cylinder.FourByFourMatching

variable {K : Type*} [Field K]

theorem partner_eq_of_collinear (A : NormalizedSystem K) (B : A.B)
    (P Q : A.W) (hPQ : P ≠ Q) (hc : Collinear P.val Q.val B.val) : partner A B P = Q := by
  have hex := exists_unique_partner A.W A.B A.arc A.disjoint A.blocks A.card P.val P.property B
  change hex.choose = Q
  exact (hex.choose_spec.2 Q ⟨fun h => hPQ (Subtype.ext h.symm), hc⟩).symm

theorem partner_distinct_black (A : NormalizedSystem K) (B C : A.B) (hBC : B ≠ C) (P : A.W) :
    partner A B P ≠ partner A C P := by
  apply partner_ne_of_other_secant A B C hBC P (partner A C P)
    (blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card C P).symm
  exact (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card C P).2

structure FourCompletion (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) where
  X : A.W
  Y : A.W
  D : A.B
  hXQ : X ≠ T.Q
  hYV : Y ≠ T.V
  hXY : X ≠ Y
  hXU : X ≠ T.U
  hYP : Y ≠ T.P
  firstX : Collinear T.Q.val X.val (firstCross A T).val
  firstY : Collinear T.V.val Y.val (firstCross A T).val
  secondXY : Collinear X.val Y.val (secondCross A T).val
  fourthUX : Collinear T.U.val X.val D.val
  fourthYP : Collinear Y.val T.P.val D.val
  zero : g D.val.rep i = 0
  ne_base : D ≠ R
  ne_first : D ≠ firstCross A T
  ne_second : D ≠ secondCross A T

set_option maxHeartbeats 1000000 in
theorem exists_four_completion (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3)
    (htwo : (2 : K) ≠ 0) (hcard : (coordinateBlacks A g i).card = 4)
    (hR : g R.val.rep i = 0) (hB : g (firstCross A T).val.rep i = 0)
    (hC : g (secondCross A T).val.rep i = 0) : Nonempty (FourCompletion A T g i) := by
  let B := firstCross A T
  let C := secondCross A T
  have hRB : R ≠ B := base_ne_first A T
  have hRC : R ≠ C := base_ne_second A T
  have hBC : B ≠ C := opposite_secants_ne A T
  have h3 : ({R, B, C} : Finset A.B).card = 3 := by simp [hRB, hRC, hBC]
  have hex : ∃ D ∈ coordinateBlacks A g i, D ∉ ({R, B, C} : Finset A.B) := by
    by_contra h
    have hsub : coordinateBlacks A g i ⊆ ({R, B, C} : Finset A.B) := by
      intro D hD
      by_contra hnot
      exact h ⟨D, hD, hnot⟩
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨D, hD, hDnot⟩ := hex
  have hDR : D ≠ R := fun h => hDnot (Finset.mem_insert.mpr (Or.inl h))
  have hDB : D ≠ B := fun h => hDnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h))))
  have hDC : D ≠ C := fun h => hDnot (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))))
  let L : Fin 4 → A.B := ![R, B, C, D]
  have hL : Function.Injective L := by
    intro k l he
    fin_cases k <;> fin_cases l <;> simp_all [L]
  have hLm : ∀ k, L k ∈ coordinateBlacks A g i := by
    intro k
    fin_cases k
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩
    · exact hD
  let M : Fin 4 → A.W → A.W := fun k => partner A (L k)
  have hinv : ∀ k, Function.Involutive (M k) := fun k =>
    blackPartner_involutive A.W A.B A.arc A.disjoint A.blocks A.card (L k)
  have hsep : ∀ k l, k ≠ l → ∀ P, M k P ≠ M l P := fun k l hkl P =>
    partner_distinct_black A (L k) (L l) (fun h => hkl (hL h)) P
  let F := coordinateFiber A g i (g (A.E T.P) i)
  let G := coordinateFiber A g i (-g (A.E T.P) i)
  have hF : F.card = 4 := (coordinateFiber_card A g i htwo (by omega) T.P).trans hcard
  have hG : G.card = 4 := (negative_coordinateFiber_card A g i htwo (by omega) T.P).trans hcard
  have hFG : ∀ k P, P ∈ F → M k P ∈ G := by
    intro k P hP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hh := partner_coordinate_flip A g i (L k) (hLm k) P
    exact hh.trans (congrArg Neg.neg (Finset.mem_filter.mp hP).2)
  have hGF : ∀ k P, P ∈ G → M k P ∈ F := by
    intro k P hP
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hh := partner_coordinate_flip A g i (L k) (hLm k) P
    exact hh.trans ((congrArg Neg.neg (Finset.mem_filter.mp hP).2).trans (neg_neg _))
  have hRP : partner A R T.P = T.Q := partner_eq_of_collinear A R T.P T.Q T.hPQ T.first_collinear
  have hRV : partner A R T.V = T.U := partner_eq_of_collinear A R T.V T.U T.hUV.symm
    (collinear_swap _ _ _ T.second_collinear)
  have hBP : partner A B T.P = T.U := partner_eq_of_collinear A B T.P T.U T.hPU
    (secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card T.P T.U T.hPU)
  have hCV : partner A C T.V = T.Q := partner_eq_of_collinear A C T.V T.Q T.hQV.symm
    (collinear_swap _ _ _ (secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.V T.hQV))
  have hP : T.P ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hQ : T.Q ∈ G := by
    have hh := hFG 0 T.P hP
    change partner A R T.P ∈ G at hh
    rwa [hRP] at hh
  have hU : T.U ∈ G := by
    have hh := hFG 1 T.P hP
    change partner A B T.P ∈ G at hh
    rwa [hBP] at hh
  have hV : T.V ∈ F := by
    have hh := hGF 0 T.U hU
    change partner A R T.U ∈ F at hh
    have hRU := partner_eq_of_collinear A R T.U T.V T.hUV T.second_collinear
    rwa [hRU] at hh
  have hentries := forced_entries F G hF hG M hinv hsep hFG hGF T.P T.V T.Q T.U
    hP hV hQ hU T.hPV T.hQU (by exact hRP) (by exact hRV) (by exact hBP) (by exact hCV)
  change partner A C (partner A B T.Q) = partner A B T.V ∧
    partner A D T.P = partner A B T.V ∧ partner A D T.U = partner A B T.Q at hentries
  let X := partner A B T.Q
  let Y := partner A B T.V
  have hXY : X ≠ Y := fun h => T.hQV ((hinv 1).injective h)
  have hXU : X ≠ T.U := fun h =>
    blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card D T.U (hentries.2.2.trans h)
  have hYP : Y ≠ T.P := fun h =>
    blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card D T.P (hentries.2.1.trans h)
  refine ⟨{
    X := X, Y := Y, D := D,
    hXQ := blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card B T.Q,
    hYV := blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card B T.V,
    hXY := hXY, hXU := hXU, hYP := hYP,
    firstX := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card B T.Q).2,
    firstY := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card B T.V).2,
    secondXY := ?_, fourthUX := ?_, fourthYP := ?_,
    zero := (Finset.mem_filter.mp hD).2, ne_base := hDR, ne_first := hDB, ne_second := hDC }⟩
  · have hh := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card C X).2
    change Collinear X.val (partner A C X).val C.val at hh
    rwa [hentries.1] at hh
  · have hh := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card D T.U).2
    change Collinear T.U.val (partner A D T.U).val D.val at hh
    rwa [hentries.2.2] at hh
  · have hh := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card D T.P).2
    change Collinear T.P.val (partner A D T.P).val D.val at hh
    rw [hentries.2.1] at hh
    exact collinear_swap _ _ _ hh

end Cylinder.BMMFourSecantMatchings

end
