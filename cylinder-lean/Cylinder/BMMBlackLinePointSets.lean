module

public import Cylinder.BMMBlackLineBlocks

/-! Literal projective point sets for the positive block, negative block,
and the fixed black line. Every black point supplies a genuine collinear
bijection of the two white blocks. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlackLinePointSets

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks

variable {K : Type*} [Field K]

def pointFiber (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) : Finset (PlanePoint K) :=
  (whiteFiber A l a).image (fun P : A.W => P.val)

def pointLineBlacks (A : NormalizedSystem K) (l : Fin 3 → K) : Finset (PlanePoint K) :=
  (lineBlacks A l).image (fun R : A.B => R.val)

def pointFiberEquiv (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) :
    whiteFiber A l a ≃ pointFiber A l a :=
  Equiv.ofBijective (fun P => ⟨P.val.val, Finset.mem_image.mpr ⟨P.val, P.property, rfl⟩⟩) (by
    constructor
    · intro P Q h
      exact Subtype.ext (Subtype.ext (congrArg (fun R : pointFiber A l a => R.val) h))
    · intro P
      obtain ⟨Q, hQ, heq⟩ := Finset.mem_image.mp P.property
      exact ⟨⟨Q, hQ⟩, Subtype.ext heq⟩)

def pointLineEquiv (A : NormalizedSystem K) (l : Fin 3 → K) :
    lineBlacks A l ≃ pointLineBlacks A l :=
  Equiv.ofBijective (fun R => ⟨R.val.val, Finset.mem_image.mpr ⟨R.val, R.property, rfl⟩⟩) (by
    constructor
    · intro P Q h
      exact Subtype.ext (Subtype.ext (congrArg (fun R : pointLineBlacks A l => R.val) h))
    · intro R
      obtain ⟨Q, hQ, heq⟩ := Finset.mem_image.mp R.property
      exact ⟨⟨Q, hQ⟩, Subtype.ext heq⟩)

theorem pointFiberEquiv_symm_val (A : NormalizedSystem K) (l : Fin 3 → K) (a : K)
    (P : pointFiber A l a) : ((pointFiberEquiv A l a).symm P).val.val = P.val :=
  congrArg Subtype.val ((pointFiberEquiv A l a).apply_symm_apply P)

theorem pointLineEquiv_symm_val (A : NormalizedSystem K) (l : Fin 3 → K)
    (R : pointLineBlacks A l) : ((pointLineEquiv A l).symm R).val.val = R.val :=
  congrArg Subtype.val ((pointLineEquiv A l).apply_symm_apply R)

theorem pointFiber_card (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) :
    (pointFiber A l a).card = (whiteFiber A l a).card := by
  rw [pointFiber, Finset.card_image_of_injective _ (fun P Q h => Subtype.ext h)]

theorem pointLineBlacks_card (A : NormalizedSystem K) (l : Fin 3 → K) :
    (pointLineBlacks A l).card = (lineBlacks A l).card := by
  rw [pointLineBlacks, Finset.card_image_of_injective _ (fun P Q h => Subtype.ext h)]

theorem pointLineBlacks_eq_filter (A : NormalizedSystem K) (l : Fin 3 → K) :
    pointLineBlacks A l = A.B.filter (fun R => dot l R.rep = 0) := by
  ext R
  constructor
  · intro hR
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
    exact Finset.mem_filter.mpr ⟨Q.property, (Finset.mem_filter.mp hQ).2⟩
  · intro hR
    obtain ⟨hRB, hz⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_image.mpr ⟨⟨R, hRB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem pointFiber_subset (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) : pointFiber A l a ⊆ A.W := by
  intro P hP
  obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hP
  exact Q.property

theorem pointLineBlacks_subset (A : NormalizedSystem K) (l : Fin 3 → K) : pointLineBlacks A l ⊆ A.B := by
  intro R hR
  obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hR
  exact Q.property

theorem pointLineBlacks_on_line (A : NormalizedSystem K) (l : Fin 3 → K) :
    ∀ R ∈ pointLineBlacks A l, dot l R.rep = 0 := by
  intro R hR
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
  exact (Finset.mem_filter.mp hQ).2

theorem pointFiber_black_disjoint (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) :
    Disjoint (pointFiber A l a) (pointLineBlacks A l) :=
  Finset.disjoint_left.mpr (fun _ hP hR => Finset.disjoint_left.mp A.disjoint
    (pointFiber_subset A l a hP) (pointLineBlacks_subset A l hR))

theorem pointFibers_disjoint (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) (ha : a ≠ -a) :
    Disjoint (pointFiber A l a) (pointFiber A l (-a)) := by
  apply Finset.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨R, hR, heq⟩ := Finset.mem_image.mp hP'
  have hRQ : R = Q := Subtype.ext heq
  have hrheight := (Finset.mem_filter.mp hR).2
  rw [hRQ] at hrheight
  exact ha ((Finset.mem_filter.mp hQ).2.symm.trans hrheight)

def pointMatching (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) (R : pointLineBlacks A l) :
    pointFiber A l a ≃ pointFiber A l (-a) :=
  (pointFiberEquiv A l a).symm.trans
    ((fiberPartnerEquiv A l a ((pointLineEquiv A l).symm R).val
      ((pointLineEquiv A l).symm R).property).trans (pointFiberEquiv A l (-a)))

theorem pointMatching_collinear (A : NormalizedSystem K) (l : Fin 3 → K) (a : K)
    (R : pointLineBlacks A l) (P : pointFiber A l a) :
    Collinear P.val (pointMatching A l a R P).val R.val := by
  let P' := (pointFiberEquiv A l a).symm P
  let R' := (pointLineEquiv A l).symm R
  have h := fiberPartnerEquiv_collinear A l a R'.val R'.property P'
  change Collinear P'.val.val (partner A R'.val P'.val).val R'.val.val at h
  change Collinear P.val (partner A R'.val P'.val).val R.val
  rwa [pointFiberEquiv_symm_val, pointLineEquiv_symm_val] at h

theorem block_point_cards (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) (P : A.W) :
    (pointFiber A l (height A l P)).card = (pointLineBlacks A l).card ∧
    (pointFiber A l (-height A l P)).card = (pointLineBlacks A l).card := by
  rw [pointFiber_card, pointFiber_card, pointLineBlacks_card]
  exact ⟨positive_fiber_card A l hl htwo hm P,
    negative_fiber_card A l P htwo (white_height_ne_zero A l hl hm P)⟩

theorem blocks_union_card (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) (P : A.W) :
    (pointFiber A l (height A l P) ∪ pointFiber A l (-height A l P)).card =
      2 * (pointLineBlacks A l).card := by
  have hdisj := pointFibers_disjoint A l (height A l P)
    (height_ne_neg A l P htwo (white_height_ne_zero A l hl hm P))
  rw [Finset.card_union_of_disjoint hdisj]
  obtain ⟨hpos, hneg⟩ := block_point_cards A l hl htwo hm P
  rw [hpos, hneg]
  omega

theorem block_points_off_line (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (hm : 2 ≤ (lineBlacks A l).card) (a : K) : ∀ P ∈ pointFiber A l a, dot l P.rep ≠ 0 := by
  intro P hP
  obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hP
  exact fun hz => white_height_ne_zero A l hl hm Q ((height_zero_iff A l Q).mpr hz)

theorem blocks_union_arc (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) :
    LineCap (pointFiber A l a ∪ pointFiber A l (-a)) 2 := by
  intro c hc
  apply (Finset.card_le_card (show (pointFiber A l a ∪ pointFiber A l (-a)).filter
    (fun P => dot c P.rep = 0) ⊆ A.W.filter (fun P => dot c P.rep = 0) from ?_)).trans (A.arc c hc)
  intro P hP
  obtain ⟨hPU, hzero⟩ := Finset.mem_filter.mp hP
  apply Finset.mem_filter.mpr
  refine ⟨?_, hzero⟩
  rcases Finset.mem_union.mp hPU with hPA | hPB
  · exact pointFiber_subset A l a hPA
  · exact pointFiber_subset A l (-a) hPB

theorem point_cross_secant_blocked (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W)
    (htwo : (2 : K) ≠ 0) (hP : height A l P ≠ 0) :
    ∀ Q ∈ pointFiber A l (height A l P), ∀ R ∈ pointFiber A l (-height A l P),
      ∃ C ∈ pointLineBlacks A l, Collinear Q R C := by
  intro Q hQ R hR
  obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨hQR, hC, hcol⟩ := cross_blocker_on_line A l P Q' R' htwo hP hQ' hR'
  exact ⟨(blocker A Q' R' hQR).val, Finset.mem_image.mpr ⟨blocker A Q' R' hQR, hC, rfl⟩, hcol⟩

end Cylinder.BMMBlackLinePointSets

end
