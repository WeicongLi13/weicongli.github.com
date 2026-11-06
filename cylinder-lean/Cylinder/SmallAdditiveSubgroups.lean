module

public import Cylinder.FiniteCosetNormalization
public import Cylinder.ProductEvaluationRelation

/-! A nontrivial finite additive subgroup in characteristic p has at
least p elements. Thus the small conic blocks cannot be additive cosets
of a nontrivial subgroup. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.SmallAdditiveSubgroups

variable {K : Type*} [Field K]

theorem prime_le_card_of_nonzero (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : AddSubgroup K) [Finite H] (a : K) (ha : a ∈ H) (ha0 : a ≠ 0) :
    p ≤ Nat.card H := by
  let _ : Fintype H := Fintype.ofFinite H
  let f := ProductEvaluationRelation.primeEmbedding p (K := K)
  have hf (x : ZMod p) : f x = (x.val : K) := by
    calc
      f x = f (x.val : ZMod p) := congrArg f (ZMod.natCast_zmod_val x).symm
      _ = _ := map_natCast f _
  let g : ZMod p → H := fun x => ⟨f x * a, by
    rw [hf]
    simpa only [nsmul_eq_mul] using H.nsmul_mem ha x.val⟩
  have hg : Function.Injective g := by
    intro x y h
    apply f.injective
    exact mul_right_cancel₀ ha0 (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective g hg
  simpa only [ZMod.card, Nat.card_eq_fintype_card] using hcard

theorem small_additive_subgroup_eq_bot (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : AddSubgroup K) [Finite H] (hcard : Nat.card H < p) : H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  have ha0 : a = 0 := by
    by_contra hzero
    have hlarge := prime_le_card_of_nonzero p H a ha hzero
    omega
  simpa only [AddSubgroup.mem_bot] using ha0

theorem small_additive_subgroup_card_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : AddSubgroup K) [Finite H] (hcard : Nat.card H < p) : Nat.card H = 1 := by
  rw [small_additive_subgroup_eq_bot p H hcard]
  simp

end Cylinder.SmallAdditiveSubgroups

end
