module

public import Cylinder.BMMBlockerPairs
public import Cylinder.BlackProjectionRationalLines

/-! Fixed-black-line blocks from actual normalized white representatives.
The normalization formula is explicit data here; its construction from
the original geometry is handled by the Segre lemma. No conic is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlackLineBlocks

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlockerPairs Cylinder.BlackProjectionRationalLines

variable {K : Type*} [Field K]

structure NormalizedSystem (K : Type*) [Field K] where
  W : Finset (PlanePoint K)
  B : Finset (PlanePoint K)
  arc : LineCap W 2
  disjoint : Disjoint W B
  blocks : BlocksSecants W B
  card : B.card + 1 = W.card
  E : W → Fin 3 → K
  representatives : ∀ P, ∃ a : K, a ≠ 0 ∧ E P = a • P.val.rep
  sums : ∀ P Q (hPQ : P ≠ Q), ∃ a : K, a ≠ 0 ∧
    E P + E Q = a • (secantBlocker W B arc disjoint blocks card P Q hPQ).val.rep

abbrev blocker (A : NormalizedSystem K) (P Q : A.W) (hPQ : P ≠ Q) : A.B :=
  secantBlocker A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ

def lineBlacks (A : NormalizedSystem K) (l : Fin 3 → K) : Finset A.B :=
  Finset.univ.filter (fun R => dot l R.val.rep = 0)

def height (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W) : K := dot l (A.E P)

def whiteFiber (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) : Finset A.W :=
  Finset.univ.filter (fun P => height A l P = a)

def otherFiber (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W) : Finset A.W :=
  Finset.univ.filter (fun Q => Q ≠ P ∧ height A l Q = -height A l P)

theorem height_zero_iff (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W) :
    height A l P = 0 ↔ dot l P.val.rep = 0 := by
  obtain ⟨a, ha, hE⟩ := A.representatives P
  have he : height A l P = a * dot l P.val.rep := by
    change dotMap l (A.E P) = _
    rw [hE, map_smul, smul_eq_mul]
    rfl
  rw [he, mul_eq_zero]
  exact or_iff_right ha

theorem blocker_on_line_iff (A : NormalizedSystem K) (l : Fin 3 → K)
    (P Q : A.W) (hPQ : P ≠ Q) :
    blocker A P Q hPQ ∈ lineBlacks A l ↔ height A l Q = -height A l P := by
  obtain ⟨a, ha, hsum⟩ := A.sums P Q hPQ
  have he : height A l P + height A l Q = a * dot l (blocker A P Q hPQ).val.rep := by
    change dotMap l (A.E P) + dotMap l (A.E Q) = _
    rw [← map_add, hsum, map_smul, smul_eq_mul]
    rfl
  simp only [lineBlacks, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hline
    have hz : height A l P + height A l Q = 0 := by rw [he, hline, mul_zero]
    apply eq_neg_iff_add_eq_zero.mpr
    rwa [add_comm]
  · intro hneg
    have hz : a * dot l (blocker A P Q hPQ).val.rep = 0 := by rw [← he, hneg, add_neg_cancel]
    exact (mul_eq_zero.mp hz).resolve_left ha

def otherBlocker (A : NormalizedSystem K) (l : Fin 3 → K) (P Q : A.W)
    (hQ : Q ∈ otherFiber A l P) : A.B :=
  blocker A P Q ((Finset.mem_filter.mp hQ).2.1.symm)

theorem otherBlocker_mem (A : NormalizedSystem K) (l : Fin 3 → K) (P Q : A.W)
    (hQ : Q ∈ otherFiber A l P) : otherBlocker A l P Q hQ ∈ lineBlacks A l :=
  (blocker_on_line_iff A l P Q ((Finset.mem_filter.mp hQ).2.1.symm)).mpr
    (Finset.mem_filter.mp hQ).2.2

theorem other_fiber_card (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W) :
    (otherFiber A l P).card = (lineBlacks A l).card := by
  apply Finset.card_bij (otherBlocker A l P) (otherBlocker_mem A l P)
  · intro Q hQ R hR heq
    exact secantBlocker_injective_at A.W A.B A.arc A.disjoint A.blocks A.card P Q R
      ((Finset.mem_filter.mp hQ).2.1.symm) ((Finset.mem_filter.mp hR).2.1.symm) heq
  · intro R hR
    obtain ⟨Q, hQ, _⟩ := exists_unique_partner A.W A.B A.arc A.disjoint A.blocks A.card P.val P.property R
    have hPQ : P ≠ Q := fun h => hQ.1 (congrArg Subtype.val h.symm)
    have hsec : blocker A P Q hPQ = R :=
      secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ R hQ.2
    have hQf : Q ∈ otherFiber A l P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hPQ.symm, ?_⟩
      apply (blocker_on_line_iff A l P Q hPQ).mp
      rwa [hsec]
    exact ⟨Q, hQf, hsec⟩

theorem zero_fiber_image (A : NormalizedSystem K) (l : Fin 3 → K) :
    (whiteFiber A l 0).image (fun P : A.W => P.val) = A.W.filter (fun P => dot l P.rep = 0) := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_filter.mpr ⟨Q.property,
      (height_zero_iff A l Q).mp (Finset.mem_filter.mp hQ).2⟩
  · intro hP
    obtain ⟨hPW, hzero⟩ := Finset.mem_filter.mp hP
    let Q : A.W := ⟨P, hPW⟩
    exact Finset.mem_image.mpr ⟨Q, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (height_zero_iff A l Q).mpr hzero⟩, rfl⟩

theorem zero_fiber_card_le_two (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0) :
    (whiteFiber A l 0).card ≤ 2 := by
  rw [← Finset.card_image_of_injective _ (fun P Q h => Subtype.ext h), zero_fiber_image]
  exact A.arc l hl

theorem white_height_ne_zero (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (hm : 2 ≤ (lineBlacks A l).card) : ∀ P : A.W, height A l P ≠ 0 := by
  intro P hzero
  have hother : otherFiber A l P = (whiteFiber A l 0).erase P := by
    ext Q
    simp only [otherFiber, whiteFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, hzero, neg_zero]
  have hP : P ∈ whiteFiber A l 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
  have hcard := other_fiber_card A l P
  rw [hother, Finset.card_erase_of_mem hP] at hcard
  have hcap := zero_fiber_card_le_two A l hl
  omega

theorem height_ne_neg (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W)
    (htwo : (2 : K) ≠ 0) (hP : height A l P ≠ 0) : height A l P ≠ -height A l P := by
  intro h
  have hz : (2 : K) * height A l P = 0 := by
    calc
      _ = height A l P - -height A l P := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact hP ((mul_eq_zero.mp hz).resolve_left htwo)

theorem negative_fiber_card (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W)
    (htwo : (2 : K) ≠ 0) (hP : height A l P ≠ 0) :
    (whiteFiber A l (-height A l P)).card = (lineBlacks A l).card := by
  have hneq := height_ne_neg A l P htwo hP
  have heq : otherFiber A l P = whiteFiber A l (-height A l P) := by
    ext Q
    simp only [otherFiber, whiteFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hQP => hneq ?_, h⟩
      rwa [hQP] at h
  rw [← heq]
  exact other_fiber_card A l P

theorem positive_fiber_card (A : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0)
    (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) (P : A.W) :
    (whiteFiber A l (height A l P)).card = (lineBlacks A l).card := by
  have hn := negative_fiber_card A l P htwo (white_height_ne_zero A l hl hm P)
  obtain ⟨Q, hQ⟩ := Finset.card_pos.mp (show 0 < (whiteFiber A l (-height A l P)).card by omega)
  have hheight := (Finset.mem_filter.mp hQ).2
  have hpos := negative_fiber_card A l Q htwo (white_height_ne_zero A l hl hm Q)
  simpa only [hheight, neg_neg] using hpos

theorem fibers_disjoint (A : NormalizedSystem K) (l : Fin 3 → K) (P : A.W)
    (htwo : (2 : K) ≠ 0) (hP : height A l P ≠ 0) :
    Disjoint (whiteFiber A l (height A l P)) (whiteFiber A l (-height A l P)) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hQ'
  exact height_ne_neg A l P htwo hP ((Finset.mem_filter.mp hQ).2.symm.trans (Finset.mem_filter.mp hQ').2)

theorem cross_blocker_on_line (A : NormalizedSystem K) (l : Fin 3 → K) (P Q R : A.W)
    (htwo : (2 : K) ≠ 0) (hP : height A l P ≠ 0)
    (hQ : Q ∈ whiteFiber A l (height A l P)) (hR : R ∈ whiteFiber A l (-height A l P)) :
    ∃ hQR : Q ≠ R, blocker A Q R hQR ∈ lineBlacks A l ∧
      Collinear Q.val R.val (blocker A Q R hQR).val := by
  have hQR : Q ≠ R := by
    intro heq
    exact Finset.disjoint_left.mp (fibers_disjoint A l P htwo hP) hQ (heq ▸ hR)
  refine ⟨hQR, (blocker_on_line_iff A l Q R hQR).mpr ?_, ?_⟩
  · rw [(Finset.mem_filter.mp hQ).2]
    exact (Finset.mem_filter.mp hR).2
  · exact secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card Q R hQR

abbrev partner (A : NormalizedSystem K) (R : A.B) (P : A.W) : A.W :=
  blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R P

theorem partner_height_flip (A : NormalizedSystem K) (l : Fin 3 → K) (R : A.B)
    (hR : R ∈ lineBlacks A l) (P : A.W) : height A l (partner A R P) = -height A l P := by
  have hs := blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card R P
  have hPQ : P ≠ partner A R P := fun h => hs.1 (congrArg Subtype.val h.symm)
  have heq : blocker A P (partner A R P) hPQ = R :=
    secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card P (partner A R P) hPQ R hs.2
  apply (blocker_on_line_iff A l P (partner A R P) hPQ).mp
  rwa [heq]

theorem partner_maps_fiber (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) (R : A.B)
    (hR : R ∈ lineBlacks A l) (P : A.W) (hP : P ∈ whiteFiber A l a) :
    partner A R P ∈ whiteFiber A l (-a) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [partner_height_flip A l R hR P, (Finset.mem_filter.mp hP).2]

def fiberPartnerEquiv (A : NormalizedSystem K) (l : Fin 3 → K) (a : K) (R : A.B)
    (hR : R ∈ lineBlacks A l) : whiteFiber A l a ≃ whiteFiber A l (-a) where
  toFun P := ⟨partner A R P.val, partner_maps_fiber A l a R hR P.val P.property⟩
  invFun Q := ⟨partner A R Q.val, by
    simpa only [neg_neg] using partner_maps_fiber A l (-a) R hR Q.val Q.property⟩
  left_inv P := Subtype.ext (blackPartner_involutive A.W A.B A.arc A.disjoint A.blocks A.card R P.val)
  right_inv Q := Subtype.ext (blackPartner_involutive A.W A.B A.arc A.disjoint A.blocks A.card R Q.val)

theorem fiberPartnerEquiv_collinear (A : NormalizedSystem K) (l : Fin 3 → K) (a : K)
    (R : A.B) (hR : R ∈ lineBlacks A l) (P : whiteFiber A l a) :
    Collinear P.val.val (fiberPartnerEquiv A l a R hR P).val.val R.val :=
  (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card R P.val).2

end Cylinder.BMMBlackLineBlocks

end
