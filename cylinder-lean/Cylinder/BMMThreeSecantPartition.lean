module

public import Cylinder.TripleFiberConfigurations
public import Cylinder.BMMBlackLinePartition
public import Cylinder.BMMSpecialFourTuple

/-! Actual matching pairs on a fixed three-secant are partitioned by
height squared into triples. Deleting each pair gives an injective family
of unordered configurations of two actual white pairs. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMThreeSecantPartition
open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlackLineBlocks
open Cylinder.InvolutionPairRepresentatives Cylinder.TripleFiberConfigurations

theorem subtype_filter_card {I J : Type*} [Fintype I] (S : Finset I) (k : I → J) (a : J) :
    ((Finset.univ : Finset S).filter (fun x => k x.val = a)).card = (S.filter (fun x => k x = a)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, rfl⟩

theorem subtype_filter_sum {I J V : Type*} [Fintype I] [AddCommMonoid V]
    (S : Finset I) (k : I → J) (a : J) (v : I → V) :
    (∑ x ∈ (Finset.univ : Finset S).filter (fun x => k x.val = a), v x.val) =
      ∑ x ∈ S.filter (fun x => k x = a), v x := by
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, rfl⟩
  · intro x _
    rfl

variable {K : Type*} [Field K]

abbrev matchingPairs (N : NormalizedSystem K) (R : N.B) : Finset N.W := pairRepresentatives (partner N R)

def squareHeight (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B) (P : matchingPairs N R) : K :=
  height N l P.val ^ 2

def squareFiber (N : NormalizedSystem K) (l : Fin 3 → K) (P : N.W) : Finset N.W :=
  Finset.univ.filter (fun Q => height N l Q ^ 2 = height N l P ^ 2)

theorem squareFiber_eq (N : NormalizedSystem K) (l : Fin 3 → K) (P : N.W) :
    squareFiber N l P = whiteFiber N l (height N l P) ∪ whiteFiber N l (-height N l P) := by
  ext Q
  simp only [squareFiber, whiteFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, sq_eq_sq_iff_eq_or_eq_neg]

theorem squareFiber_card (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : (lineBlacks N l).card = 3) (P : N.W) :
    (squareFiber N l P).card = 6 := by
  have hm2 : 2 ≤ (lineBlacks N l).card := by omega
  rw [squareFiber_eq, Finset.card_union_of_disjoint
    (fibers_disjoint N l P htwo (white_height_ne_zero N l hl hm2 P)),
    positive_fiber_card N l hl htwo hm2 P,
    negative_fiber_card N l P htwo (white_height_ne_zero N l hl hm2 P), hm]

theorem matching_square_fiber_card (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : (lineBlacks N l).card = 3) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R) :
    (fiber (squareHeight N l R) P).card = 3 := by
  have hc := pairRepresentatives_fiber_card (partner N R)
    (blackPartner_involutive N.W N.B N.arc N.disjoint N.blocks N.card R)
    (blackPartner_ne N.W N.B N.arc N.disjoint N.blocks N.card R)
    (fun Q => height N l Q ^ 2) (fun Q => by rw [partner_height_flip N l R hR Q, neg_sq])
    (height N l P.val ^ 2)
  have hsc := squareFiber_card N l hl htwo hm P.val
  have hsub := subtype_filter_card (matchingPairs N R) (fun Q => height N l Q ^ 2) (height N l P.val ^ 2)
  change (fiber (squareHeight N l R) P).card = _ at hsub
  change 2 * _ = (squareFiber N l P.val).card at hc
  rw [hsc, ← hsub] at hc
  omega

def pairIndices (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (P : matchingPairs N R) : Finset (matchingPairs N R) := configuration (squareHeight N l R) P

def whitePair (N : NormalizedSystem K) (R : N.B) (P : matchingPairs N R) : Finset (PlanePoint K) :=
  {P.val.val, (partner N R P.val).val}

theorem whitePair_injective (N : NormalizedSystem K) (R : N.B) : Function.Injective (whitePair N R) := by
  intro P Q heq
  have hp : P.val.val ∈ whitePair N R Q := heq ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hp with hp | hp
  · exact Subtype.ext (Subtype.ext hp)
  · have hPQ : P.val = partner N R Q.val := Subtype.ext (Finset.mem_singleton.mp hp)
    exact False.elim (representative_partner_not_mem (partner N R)
      (blackPartner_involutive N.W N.B N.arc N.disjoint N.blocks N.card R)
      Q.val Q.property (hPQ ▸ P.property))

def configurationKey (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (P : matchingPairs N R) : Finset (Finset (PlanePoint K)) := (pairIndices N l R P).image (whitePair N R)

theorem pairIndices_card (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : (lineBlacks N l).card = 3) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R) : (pairIndices N l R P).card = 2 :=
  configuration_card _ (matching_square_fiber_card N l hl htwo hm R hR) P

theorem configurationKey_injective (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : (lineBlacks N l).card = 3) (R : N.B)
    (hR : R ∈ lineBlacks N l) : Function.Injective (configurationKey N l R) := by
  intro P Q heq
  exact configuration_injective _ (matching_square_fiber_card N l hl htwo hm R hR)
    ((Finset.image_injective (whitePair_injective N R)) heq)

theorem configurationKey_card (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : (lineBlacks N l).card = 3) (R : N.B)
    (hR : R ∈ lineBlacks N l) (n : ℕ) (hn : N.W.card = 2 * n) :
    (Finset.univ.image (configurationKey N l R)).card = n := by
  rw [Finset.card_image_of_injective _ (configurationKey_injective N l hl htwo hm R hR),
    Finset.card_univ, Fintype.card_coe]
  have hc := pairRepresentatives_card (partner N R)
    (blackPartner_involutive N.W N.B N.arc N.disjoint N.blocks N.card R)
    (blackPartner_ne N.W N.B N.arc N.disjoint N.blocks N.card R)
  rw [Fintype.card_coe, hn] at hc
  change 2 * (matchingPairs N R).card = 2 * n at hc
  omega

end Cylinder.BMMThreeSecantPartition
end
