module

public import Cylinder.BMMBlackLineBlocks
public import Cylinder.BMMMatchingParity

/-! The actual height fibers partition the normalized white set. Every
fiber has the black-line size and the occurring heights pair under negation,
proving the divisibility in BMM Lemma 4 without a conic hypothesis. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMBlackLinePartition

open Cylinder.BMMBlackLineBlocks

variable {K : Type*} [Field K]

def heightValues (A : NormalizedSystem K) (l : Fin 3 → K) : Finset K :=
  Finset.univ.image (height A l)

theorem occurring_fiber_card (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) (a : K) (ha : a ∈ heightValues A l) :
    (whiteFiber A l a).card = (lineBlacks A l).card := by
  obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp ha
  exact positive_fiber_card A l hl htwo hm P

theorem card_eq_heightValues_mul_line (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) :
    A.W.card = (heightValues A l).card * (lineBlacks A l).card := by
  have hc := Finset.card_eq_sum_card_image (height A l) (Finset.univ : Finset A.W)
  change (Finset.univ : Finset A.W).card = ∑ a ∈ heightValues A l, (whiteFiber A l a).card at hc
  simp only [Finset.card_univ, Fintype.card_coe] at hc
  rw [hc]
  calc
    _ = ∑ _a ∈ heightValues A l, (lineBlacks A l).card := Finset.sum_congr rfl
      (fun a ha => occurring_fiber_card A l hl htwo hm a ha)
    _ = _ := by simp

theorem occurring_height_nonzero (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (hm : 2 ≤ (lineBlacks A l).card) (a : K) (ha : a ∈ heightValues A l) : a ≠ 0 := by
  obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp ha
  exact white_height_ne_zero A l hl hm P

theorem neg_mem_heightValues (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) (a : K) (ha : a ∈ heightValues A l) :
    -a ∈ heightValues A l := by
  obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp ha
  have hc := negative_fiber_card A l P htwo (white_height_ne_zero A l hl hm P)
  obtain ⟨Q, hQ⟩ := Finset.card_pos.mp (show 0 < (whiteFiber A l (-height A l P)).card by omega)
  exact Finset.mem_image.mpr ⟨Q, Finset.mem_univ _, (Finset.mem_filter.mp hQ).2⟩

def negateHeight (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) : heightValues A l → heightValues A l :=
  fun a => ⟨-a.val, neg_mem_heightValues A l hl htwo hm a.val a.property⟩

theorem heightValues_card_even (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) : Even (heightValues A l).card := by
  have hi : Function.Involutive (negateHeight A l hl htwo hm) := fun a => Subtype.ext (neg_neg a.val)
  have hfree : ∀ a, negateHeight A l hl htwo hm a ≠ a := by
    intro a heq
    have hneg : -a.val = a.val := congrArg Subtype.val heq
    have hzero : (2 : K) * a.val = 0 := by
      calc
        _ = a.val - -a.val := by ring
        _ = 0 := sub_eq_zero.mpr hneg.symm
    exact occurring_height_nonzero A l hl hm a.val a.property ((mul_eq_zero.mp hzero).resolve_left htwo)
  have heven := BMMMatchingParity.fixed_point_free_involution_even_card
    (negateHeight A l hl htwo hm) hi hfree
  simpa only [Fintype.card_coe] using heven

theorem white_card_multiple_twice_line (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) :
    ∃ k : ℕ, A.W.card = 2 * (lineBlacks A l).card * k := by
  obtain ⟨k, hk⟩ := heightValues_card_even A l hl htwo hm
  have hc := card_eq_heightValues_mul_line A l hl htwo hm
  refine ⟨k, ?_⟩
  rw [hk] at hc
  exact hc.trans (by ring)

theorem line_card_dvd_half_white (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 1 ≤ (lineBlacks A l).card) (n : ℕ) (hn : A.W.card = 2 * n) :
    (lineBlacks A l).card ∣ n := by
  by_cases hone : (lineBlacks A l).card = 1
  · rw [hone]; exact one_dvd n
  have hm2 : 2 ≤ (lineBlacks A l).card := by omega
  obtain ⟨k, hk⟩ := white_card_multiple_twice_line A l hl htwo hm2
  refine ⟨k, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * n = A.W.card := hn.symm
    _ = 2 * (lineBlacks A l).card * k := hk
    _ = 2 * ((lineBlacks A l).card * k) := by ring

end Cylinder.BMMBlackLinePartition

end
