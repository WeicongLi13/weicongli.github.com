module

public import Cylinder.BMMMatchingParity
public import Cylinder.BMMCocycleNormalization

/-! Three disjoint pairs in an actual blocker matching, and the elementary
non-special-pair argument used in the BMM classification. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMSpecialPairs

set_option backward.isDefEq.respectTransparency false

theorem exists_outside_of_card_lt {I : Type*} [Fintype I] (s : Finset I)
    (hs : s.card < Fintype.card I) : ∃ x : I, x ∉ s := by
  by_contra! h
  have hsub : Finset.univ ⊆ s := fun x _ => h x
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ] at hc
  omega

theorem exists_three_disjoint_pairs {I : Type*} [Fintype I]
    (f : I → I) (hinv : Function.Involutive f) (hfree : ∀ x, f x ≠ x)
    (hcard : 4 < Fintype.card I) :
    ∃ a b c : I, f a ≠ a ∧ f b ≠ b ∧ f c ≠ c ∧ b ∉ ({a, f a} : Finset I) ∧
      f b ∉ ({a, f a} : Finset I) ∧
      c ∉ ({a, f a, b, f b} : Finset I) ∧
      f c ∉ ({a, f a, b, f b} : Finset I) := by
  obtain ⟨a, _⟩ := exists_outside_of_card_lt (∅ : Finset I) (by simp; omega)
  obtain ⟨b, hb⟩ := exists_outside_of_card_lt ({a, f a} : Finset I)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hfb : f b ∉ ({a, f a} : Finset I) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb ⊢
    constructor
    · intro h
      exact hb.2 (by simpa only [hinv b] using congrArg f h)
    · intro h
      exact hb.1 (hinv.injective h)
  obtain ⟨c, hc⟩ := exists_outside_of_card_lt ({a, f a, b, f b} : Finset I)
    (lt_of_le_of_lt Finset.card_le_four hcard)
  have hfc : f c ∉ ({a, f a, b, f b} : Finset I) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hc.2.1 (by simpa only [hinv c] using congrArg f h)
    · intro h
      exact hc.1 (hinv.injective h)
    · intro h
      exact hc.2.2.2 (by simpa only [hinv c] using congrArg f h)
    · intro h
      exact hc.2.2.1 (hinv.injective h)
  exact ⟨a, b, c, hfree a, hfree b, hfree c, hb, hfb, hc, hfc⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem two_special_pairs_force_third_not_special (htwo : (2 : K) ≠ 0)
    (u v w : V) (hv : v ≠ 0) (huv : u + v = 0) (huw : u + w = 0) : v + w ≠ 0 := by
  have hvw : v = w := add_left_cancel (huv.trans huw.symm)
  intro h
  have htwov : (2 : K) • v = 0 := by simpa only [← hvw, two_smul K v] using h
  exact hv ((smul_eq_zero.mp htwov).resolve_left htwo)

theorem exists_nonspecial_pair (htwo : (2 : K) ≠ 0) (u v w : V) (hv : v ≠ 0) :
    u + v ≠ 0 ∨ u + w ≠ 0 ∨ v + w ≠ 0 := by
  by_cases huv : u + v = 0
  · by_cases huw : u + w = 0
    · exact Or.inr (Or.inr (two_special_pairs_force_third_not_special htwo u v w hv huv huw))
    · exact Or.inr (Or.inl huw)
  · exact Or.inl huv

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry

theorem actual_black_matching_three_pairs (W B : Finset (PlanePoint K)) (hW : LineCap W 2)
    (hdisj : Disjoint W B) (hblock : BlocksSecants W B) (hcard : B.card + 1 = W.card)
    (R : B) (hlarge : 4 < W.card) :
    let f := blackPartner W B hW hdisj hblock hcard R
    ∃ a b c : W, f a ≠ a ∧ f b ≠ b ∧ f c ≠ c ∧ b ∉ ({a, f a} : Finset W) ∧
      f b ∉ ({a, f a} : Finset W) ∧
      c ∉ ({a, f a, b, f b} : Finset W) ∧
      f c ∉ ({a, f a, b, f b} : Finset W) := by
  dsimp only
  simpa only [Finset.mem_insert, Finset.mem_singleton] using exists_three_disjoint_pairs _
    (blackPartner_involutive W B hW hdisj hblock hcard R)
    (blackPartner_ne W B hW hdisj hblock hcard R)
    (by simpa only [Fintype.card_coe] using hlarge)

theorem scaled_representative_sum_ne_zero (P Q : PlanePoint K) (hPQ : P ≠ Q)
    (α β : K) (hβ : β ≠ 0) : α • P.rep + β • Q.rep ≠ 0 := by
  intro hz
  apply representatives_not_proportional P Q hPQ (-α / β)
  calc
    Q.rep = β⁻¹ • (β • Q.rep) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
    _ = β⁻¹ • (-(α • P.rep)) := by rw [eq_neg_of_add_eq_zero_right hz]
    _ = (-α / β) • P.rep := by
      rw [smul_neg, smul_smul, ← neg_smul]
      congr 1
      rw [div_eq_mul_inv]
      ring

end Cylinder.BMMSpecialPairs

end
