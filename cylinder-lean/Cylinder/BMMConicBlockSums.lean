module

public import Cylinder.BMMConicBlockCosets
public import Cylinder.ConicCosetVectorSums

/-! The original normalized vectors in opposite conic blocks sum to zero.
The result uses the same field embedding and coordinates on both blocks. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMConicBlockSums

open Cylinder.ProjectiveFieldEmbedding Cylinder.BMMBlackLineBlocks
open Cylinder.BMMBlackLinePointSets Cylinder.ConicNormalizedBlockVectors
open Cylinder.BMMConicBlockCosets Cylinder.ConicCosetVectorSums
open Cylinder.ConicRootPairsGeometry

variable {R K : Type*} [Field R] [Field K]

theorem original_block_sum_zero (ι : R →+* K) (N : NormalizedSystem R)
    (l : Fin 3 → R) (h : R) (m : ℕ) (D : HyperbolaBlockData ι N l h m)
    (hm : 1 < m) :
    (∑ P : pointFiber N l h, N.E (fiberWhite N l h P)) +
      (∑ P : pointFiber N l (-h), N.E (fiberWhite N l (-h) P)) = 0 := by
  let : Finite D.H := D.finite
  let : Fintype D.H := Fintype.ofFinite D.H
  have hc : 1 < Fintype.card D.H := by
    rw [← Nat.card_eq_fintype_card, D.card]
    exact hm
  have hpos :
      (∑ P : pointFiber N l h, D.g (vectorMap ι (N.E (fiberWhite N l h P)))) =
        ∑ t : D.H, D.c • hyperbolaVector (D.a * t.val) :=
    Fintype.sum_equiv D.posEquiv _ _ D.pos_vectors
  have hneg :
      (∑ P : pointFiber N l (-h), D.g (vectorMap ι (N.E (fiberWhite N l (-h) P)))) =
        ∑ t : D.H, (-D.c) • hyperbolaVector (D.b * t.val) :=
    Fintype.sum_equiv D.negEquiv _ _ D.neg_vectors
  apply vectorMap_injective ι
  apply D.g.injective
  simp only [map_add, map_sum, map_zero]
  rw [hpos, hneg]
  exact opposite_hyperbola_blocks_sum_zero D.H hc D.a D.b D.c

open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData
open Cylinder.BMMNormalizedGeometry

theorem actual_prime_block_sum_zero (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (A : Configuration (ZMod p)) (anchor : A.W)
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) (hm : 3 ≤ (blackLine A l).card) :
    let N := normalizedSystem A anchor
    let h := height N l anchor
    (∑ P : pointFiber N l h, N.E (fiberWhite N l h P)) +
      (∑ P : pointFiber N l (-h), N.E (fiberWhite N l (-h) P)) = 0 := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨D⟩ := exists_actual_block_coset_data p (K := K) hp A anchor l hl hm
  exact original_block_sum_zero _ _ _ _ _ D (by omega)

variable {V : Type*} [AddCommGroup V]

theorem three_nonzero_pair_sums (u v w : V) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hsum : u + v + w = 0) : u + v ≠ 0 ∧ u + w ≠ 0 ∧ v + w ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hw
    simpa only [h, zero_add] using hsum
  · intro h
    apply hv
    have he : u + v + w = (u + w) + v := by abel
    simpa only [he, h, zero_add] using hsum
  · intro h
    apply hu
    have he : u + v + w = u + (v + w) := by abel
    simpa only [he, h, add_zero] using hsum

end Cylinder.BMMConicBlockSums

end
