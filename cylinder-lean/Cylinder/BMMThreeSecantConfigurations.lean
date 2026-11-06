module

public import Cylinder.BMMThreeSecantPartition
public import Cylinder.BMMFixedNormalizationBlockSums

/-! A fixed real three-secant produces as many different nonspecial
four-point configurations as matching pairs. All vectors use the same
normalization; their six-point zero sums are proved from the conic. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMThreeSecantConfigurations
open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlackLineBlocks
open Cylinder.BMMActualCoefficients Cylinder.BMMSpecialFourTuple
open Cylinder.InvolutionPairRepresentatives Cylinder.TripleFiberConfigurations
open Cylinder.BMMThreeSecantPartition Cylinder.BMMFixedNormalizationBlockSums
open Cylinder.BMMFinitePlaneArcBound

variable {K : Type*} [Field K]

def systemConfiguration (N : NormalizedSystem K) : Configuration K :=
  ⟨N.W, N.B, N.arc, N.disjoint, N.blocks, N.card⟩

def pairVector (N : NormalizedSystem K) (R : N.B) (P : matchingPairs N R) : Fin 3 → K :=
  N.E P.val + N.E (partner N R P.val)

theorem pairVector_ne_zero (N : NormalizedSystem K) (R : N.B) (P : matchingPairs N R) :
    pairVector N R P ≠ 0 := by
  have hP : P.val ≠ partner N R P.val :=
    (blackPartner_ne N.W N.B N.arc N.disjoint N.blocks N.card R P.val).symm
  obtain ⟨a, ha, hE⟩ := N.sums P.val (partner N R P.val) hP
  change N.E P.val + N.E (partner N R P.val) ≠ 0
  rw [hE]
  exact smul_ne_zero ha (blocker N P.val (partner N R P.val) hP).val.rep_nonzero

theorem square_fiber_vector_sum_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (P : N.W) :
    (∑ Q ∈ squareFiber N l P, N.E Q) = 0 := by
  have htwo := prime_two_nonzero p hp
  have hm2 : 2 ≤ (lineBlacks N l).card := by omega
  rw [squareFiber_eq, Finset.sum_union
    (fibers_disjoint N l P htwo (white_height_ne_zero N l hl hm2 P))]
  exact fixed_normalization_block_sum_zero p hp N l hl (by omega) P

set_option maxHeartbeats 1000000 in
theorem matching_fiber_vector_sum_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (R : N.B) (hR : R ∈ lineBlacks N l)
    (P : matchingPairs N R) :
    (∑ Q ∈ fiber (squareHeight N l R) P, pairVector N R Q) = 0 := by
  let : DecidableEq (ZMod p) := Classical.decEq _
  let f := partner N R
  have hs := stable_sum_eq_sum_pairs f
    (blackPartner_involutive N.W N.B N.arc N.disjoint N.blocks N.card R)
    (blackPartner_ne N.W N.B N.arc N.disjoint N.blocks N.card R)
    (squareFiber N l P.val) (by
      intro Q hQ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change height N l (partner N R Q) ^ 2 = height N l P.val ^ 2
      rw [partner_height_flip N l R hR, neg_sq]
      exact (Finset.mem_filter.mp hQ).2) N.E
  have heq : (squareFiber N l P.val).filter (fun Q => rank Q < rank (f Q)) =
      (matchingPairs N R).filter (fun Q => height N l Q ^ 2 = height N l P.val ^ 2) := by
    ext Q
    simp only [squareFiber, matchingPairs, pairRepresentatives, Finset.mem_filter, Finset.mem_univ,
      true_and, and_comm, f]
  rw [square_fiber_vector_sum_zero p hp N l hl hm, heq] at hs
  have hsub := subtype_filter_sum (matchingPairs N R) (fun Q => height N l Q ^ 2)
    (height N l P.val ^ 2) (fun Q => N.E Q + N.E (partner N R Q))
  change (∑ Q ∈ fiber (squareHeight N l R) P, pairVector N R Q) = _ at hsub
  exact hsub.trans (by simpa only [f] using hs.symm)

theorem configuration_vector_sum_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (R : N.B) (hR : R ∈ lineBlacks N l)
    (P : matchingPairs N R) :
    (∑ Q ∈ pairIndices N l R P, pairVector N R Q) ≠ 0 :=
  configuration_sum_ne_zero _ _ (pairVector_ne_zero N R)
    (matching_fiber_vector_sum_zero p hp N l hl hm R hR) P

def fourTupleKey (N : NormalizedSystem K) (R : N.B)
    (T : FourTuple (systemConfiguration N) N.E R) : Finset (Finset (PlanePoint K)) :=
  {{T.P.val, T.Q.val}, {T.U.val, T.V.val}}

set_option maxHeartbeats 1000000 in
theorem exists_configuration_fourtuple (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (R : N.B) (hR : R ∈ lineBlacks N l)
    (P : matchingPairs N R) :
    ∃ T : FourTuple (systemConfiguration N) N.E R, fourTupleKey N R T = configurationKey N l R P := by
  obtain ⟨U, V, hUV, hset⟩ := Finset.card_eq_two.mp
    (pairIndices_card N l hl (prime_two_nonzero p hp) hm R hR P)
  have hd := distinct_representative_pairs (partner N R)
    (blackPartner_involutive N.W N.B N.arc N.disjoint N.blocks N.card R) U V hUV
  have hn := configuration_vector_sum_ne_zero p hp N l hl hm R hR P
  rw [hset, Finset.sum_pair hUV] at hn
  let T := matchingFourTuple (systemConfiguration N) N.E R U.val V.val
    hd.1.symm hd.2.2.1.symm hd.2.1.symm hd.2.2.2.symm hn
  refine ⟨T, ?_⟩
  change {{U.val.val, (partner N R U.val).val}, {V.val.val, (partner N R V.val).val}} =
    (pairIndices N l R P).image (whitePair N R)
  rw [hset, Finset.image_insert, Finset.image_singleton]
  rfl

theorem exists_indexed_nonspecial_configurations (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (R : N.B) (hR : R ∈ lineBlacks N l)
    (n : ℕ) (hn : N.W.card = 2 * n) :
    ∃ T : matchingPairs N R → FourTuple (systemConfiguration N) N.E R,
      Function.Injective (fun P => fourTupleKey N R (T P)) ∧ Fintype.card (matchingPairs N R) = n := by
  choose T hT using exists_configuration_fourtuple p hp N l hl hm R hR
  refine ⟨T, ?_, ?_⟩
  · intro P Q heq
    change fourTupleKey N R (T P) = fourTupleKey N R (T Q) at heq
    rw [hT P, hT Q] at heq
    exact configurationKey_injective N l hl (prime_two_nonzero p hp) hm R hR heq
  · have hc := configurationKey_card N l hl (prime_two_nonzero p hp) hm R hR n hn
    rw [Finset.card_image_of_injective _
      (configurationKey_injective N l hl (prime_two_nonzero p hp) hm R hR), Finset.card_univ] at hc
    exact hc

end Cylinder.BMMThreeSecantConfigurations
end
