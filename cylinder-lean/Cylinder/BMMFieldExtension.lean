module

public import Cylinder.BMMActualBlackLineData

/-! The actual BMM configuration after a field embedding. Extension
field lines preserve the arc bound, and canonical representative units
preserve the true collinearity and base-field line intersections. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFieldExtension

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct
open Cylinder.PlaneLinearForms Cylinder.PowerEvaluationRelation
open Cylinder.ProjectiveFieldEmbedding Cylinder.BlackProjectionRationalLines
open Cylinder.BMMArcGeometry Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData

variable {K L : Type*} [Field K] [Field L]

theorem dot_pointMap_rep (f : K →+* L) (l : Fin 3 → L) (P : PlanePoint K) :
    dot l (pointMap f P).rep =
      (representativeUnit f P : L) * dot l (vectorMap f P.rep) := by
  change dotMap l (pointMap f P).rep = _
  rw [← representativeUnit_spec f P, map_smul, smul_eq_mul]
  rfl

theorem linezero_iff (f : K →+* L) (l : Fin 3 → L) (P : PlanePoint K) :
    dot l (pointMap f P).rep = 0 ↔ dot l (vectorMap f P.rep) = 0 := by
  rw [dot_pointMap_rep, mul_eq_zero]
  exact or_iff_right (Units.ne_zero (representativeUnit f P))

theorem mapped_linezero_iff (f : K →+* L) (l : Fin 3 → K) (P : PlanePoint K) :
    dot (vectorMap f l) (pointMap f P).rep = 0 ↔ dot l P.rep = 0 := by
  rw [linezero_iff]
  change dot (fun j => f (l j)) (fun j => f (P.rep j)) = 0 ↔ dot l P.rep = 0
  rw [← map_dot f l P.rep]
  exact map_eq_zero f

theorem imageEquiv_val (f : K →+* L) (D : Finset (PlanePoint K)) (P : D) :
    (imageEquiv f D P).val = pointMap f P.val := rfl

theorem imageSet_filter (f : K →+* L) (D : Finset (PlanePoint K))
    (pred : PlanePoint L → Prop) :
    (imageSet f D).filter pred = imageSet f (D.filter (fun P => pred (pointMap f P))) := by
  ext Q
  simp only [imageSet, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨P, hP, rfl⟩, hp⟩
    exact ⟨P, ⟨hP, hp⟩, rfl⟩
  · rintro ⟨P, ⟨hP, hp⟩, rfl⟩
    exact ⟨⟨P, hP, rfl⟩, hp⟩

theorem linearForm_nonzero (l : Fin 3 → L) (hl : l ≠ 0) : linearForm l ≠ 0 := by
  intro hz
  apply hl
  funext j
  have hj := congrArg (eval (Pi.single j 1)) hz
  simpa only [eval_single_linearForm, map_zero, Pi.zero_apply] using hj

theorem image_lineCap (f : K →+* L) (W : Finset (PlanePoint K)) (b : ℕ)
    (hb : 1 ≤ b) (hW : LineCap W b) : LineCap (imageSet f W) b := by
  intro l hl
  rw [imageSet_filter]
  have hfilter : W.filter (fun P => dot l (pointMap f P).rep = 0) =
      zeroSet f W (linearForm l) := by
    ext P
    simp only [zeroSet, Finset.mem_filter, eval_linearForm, linezero_iff]
    rfl
  rw [hfilter, imageSet_card]
  exact linear_factor_card_bound f W b hb hW (linearForm l) (linearFormMap l).property
    (linearForm_nonzero l hl)

theorem image_arc (f : K →+* L) (W : Finset (PlanePoint K)) (hW : LineCap W 2) :
    LineCap (imageSet f W) 2 :=
  image_lineCap f W 2 (by decide) hW

theorem triple_smul (v w x : Fin 3 → L) (a b c : L) :
    dot (cross (a • v) (b • w)) (c • x) = (a * b * c) * dot (cross v w) x := by
  simp [dot, cross, Pi.smul_apply, Fin.sum_univ_succ]
  ring

theorem pointMap_triple (f : K →+* L) (P Q R : PlanePoint K) :
    dot (cross (pointMap f P).rep (pointMap f Q).rep) (pointMap f R).rep =
      ((representativeUnit f P : L) * (representativeUnit f Q : L) * (representativeUnit f R : L)) *
        f (dot (cross P.rep Q.rep) R.rep) := by
  rw [← representativeUnit_spec f P, ← representativeUnit_spec f Q, ← representativeUnit_spec f R,
    triple_smul]
  change _ * dot (cross (fun j => f (P.rep j)) (fun j => f (Q.rep j))) (fun j => f (R.rep j)) = _
  rw [← map_cross f P.rep Q.rep, ← map_dot f (cross P.rep Q.rep) R.rep]

theorem pointMap_collinear_iff (f : K →+* L) (P Q R : PlanePoint K) :
    Collinear (pointMap f P) (pointMap f Q) (pointMap f R) ↔ Collinear P Q R := by
  change dot (cross (pointMap f P).rep (pointMap f Q).rep) (pointMap f R).rep = 0 ↔
    dot (cross P.rep Q.rep) R.rep = 0
  rw [pointMap_triple, mul_eq_zero]
  have hn := mul_ne_zero (mul_ne_zero (Units.ne_zero (representativeUnit f P))
    (Units.ne_zero (representativeUnit f Q))) (Units.ne_zero (representativeUnit f R))
  rw [or_iff_right hn]
  exact map_eq_zero f

theorem pointMap_collinear (f : K →+* L) (P Q R : PlanePoint K) (h : Collinear P Q R) :
    Collinear (pointMap f P) (pointMap f Q) (pointMap f R) :=
  (pointMap_collinear_iff f P Q R).mpr h

theorem imageSet_disjoint (f : K →+* L) (W B : Finset (PlanePoint K)) (hd : Disjoint W B) :
    Disjoint (imageSet f W) (imageSet f B) := by
  apply Finset.disjoint_left.mpr
  intro R hW hB
  obtain ⟨P, hP, hp⟩ := Finset.mem_image.mp hW
  obtain ⟨Q, hQ, hq⟩ := Finset.mem_image.mp hB
  have hPQ := pointMap_injective f (hp.trans hq.symm)
  exact Finset.disjoint_left.mp hd hP (hPQ ▸ hQ)

theorem image_blocks_secants (f : K →+* L) (W B : Finset (PlanePoint K))
    (hblock : BlocksSecants W B) : BlocksSecants (imageSet f W) (imageSet f B) := by
  intro P hP Q hQ hPQ
  obtain ⟨P0, hP0, hPmap⟩ := Finset.mem_image.mp hP
  obtain ⟨Q0, hQ0, hQmap⟩ := Finset.mem_image.mp hQ
  have hpq : P0 ≠ Q0 := by
    intro h
    exact hPQ (hPmap.symm.trans ((congrArg (pointMap f) h).trans hQmap))
  obtain ⟨R, hR, hcol⟩ := hblock P0 hP0 Q0 hQ0 hpq
  refine ⟨pointMap f R, Finset.mem_image.mpr ⟨R, hR, rfl⟩, ?_⟩
  rw [← hPmap, ← hQmap]
  exact pointMap_collinear f P0 Q0 R hcol

def imageConfiguration (f : K →+* L) (A : Configuration K) : Configuration L where
  W := imageSet f A.W
  B := imageSet f A.B
  arc := image_arc f A.W A.arc
  disjoint := imageSet_disjoint f A.W A.B A.disjoint
  blocks := image_blocks_secants f A.W A.B A.blocks
  card := by rw [imageSet_card, imageSet_card]; exact A.card

theorem image_white_card (f : K →+* L) (A : Configuration K) :
    (imageConfiguration f A).W.card = A.W.card := imageSet_card f A.W

theorem image_black_card (f : K →+* L) (A : Configuration K) :
    (imageConfiguration f A).B.card = A.B.card := imageSet_card f A.B

theorem mapped_line_nonzero (f : K →+* L) (l : Fin 3 → K) (hl : l ≠ 0) : vectorMap f l ≠ 0 := by
  intro hz
  exact hl (vectorMap_injective f (by simpa only [map_zero] using hz))

theorem image_blackLine (f : K →+* L) (A : Configuration K) (l : Fin 3 → K) :
    blackLine (imageConfiguration f A) (vectorMap f l) = imageSet f (blackLine A l) := by
  change (imageSet f A.B).filter (fun P => dot (vectorMap f l) P.rep = 0) =
    imageSet f (A.B.filter (fun P => dot l P.rep = 0))
  rw [imageSet_filter]
  congr 1
  ext P
  simp only [Finset.mem_filter, mapped_linezero_iff]

theorem image_blackLine_card (f : K →+* L) (A : Configuration K) (l : Fin 3 → K) :
    (blackLine (imageConfiguration f A) (vectorMap f l)).card = (blackLine A l).card := by
  rw [image_blackLine, imageSet_card]

end Cylinder.BMMFieldExtension

end
