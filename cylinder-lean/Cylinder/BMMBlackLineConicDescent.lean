module

public import Cylinder.BMMBlackLineConic
public import Cylinder.BMMFieldExtension
public import Cylinder.EquationScalarDescent

/-! Embed the actual base-field blocks and their collinear matchings into
an infinite extension, construct the conic there, and descend its actual
coefficients to the original field without changing the degree. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlackLineConicDescent

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.ProjectiveFieldEmbedding Cylinder.BMMFieldExtension Cylinder.LinearEvaluationTransport

variable {R K : Type*} [Field R] [Field K]

theorem image_collinear_matchings (f : R →+* K) (X Y C : Finset (PlanePoint R))
    (hmatch : ∀ B : C, ∃ e : X ≃ Y, ∀ P : X, Collinear P.val (e P).val B.val) :
    ∀ B : imageSet f C, ∃ e : imageSet f X ≃ imageSet f Y,
      ∀ P : imageSet f X, Collinear P.val (e P).val B.val := by
  intro B
  let B' := (imageEquiv f C).symm B
  obtain ⟨e, he⟩ := hmatch B'
  let e' : imageSet f X ≃ imageSet f Y :=
    (imageEquiv f X).symm.trans (e.trans (imageEquiv f Y))
  refine ⟨e', fun P => ?_⟩
  let P' := (imageEquiv f X).symm P
  have hP : pointMap f P'.val = P.val := congrArg Subtype.val ((imageEquiv f X).apply_symm_apply P)
  have hB : pointMap f B'.val = B.val := congrArg Subtype.val ((imageEquiv f C).apply_symm_apply B)
  change Collinear P.val (pointMap f (e P').val) B.val
  rw [← hP, ← hB]
  exact pointMap_collinear f P'.val (e P').val B'.val (he P')

theorem vanishing_on_image_implies_mapped_rep (f : R →+* K) (Q : MvPolynomial (Fin 3) K)
    (hQ : Q.IsHomogeneous 2) (P : PlanePoint R) (hzero : eval (pointMap f P).rep Q = 0) :
    eval (vectorMap f P.rep) Q = 0 := by
  rw [← representativeUnit_spec f P, homogeneous_eval_smul Q 2 hQ] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 (Units.ne_zero (representativeUnit f P)))

theorem conic_of_base_collinear_matchings [Infinite K] [Algebra R K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (l : Fin 3 → R) (hl : l ≠ 0)
    (X Y C : Finset (PlanePoint R)) (hdisj : Disjoint X Y)
    (hXcard : X.card = C.card) (hYcard : Y.card = C.card) (hCnon : C.Nonempty) (hCp : C.card ≤ p)
    (hXoff : ∀ P ∈ X, dot l P.rep ≠ 0) (hYoff : ∀ Q ∈ Y, dot l Q.rep ≠ 0)
    (hCline : ∀ B ∈ C, dot l B.rep = 0)
    (hmatch : ∀ B : C, ∃ e : X ≃ Y, ∀ P : X, Collinear P.val (e P).val B.val) :
    ∃ Q : MvPolynomial (Fin 3) R, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧ ∀ P ∈ X ∪ Y, eval P.rep Q = 0 := by
  let f := algebraMap R K
  have hXoff' : ∀ P ∈ imageSet f X, dot (vectorMap f l) P.rep ≠ 0 := by
    intro P hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hP
    exact fun hz => hXoff P0 hP0 ((mapped_linezero_iff f l P0).mp hz)
  have hYoff' : ∀ P ∈ imageSet f Y, dot (vectorMap f l) P.rep ≠ 0 := by
    intro P hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hP
    exact fun hz => hYoff P0 hP0 ((mapped_linezero_iff f l P0).mp hz)
  have hCline' : ∀ B ∈ imageSet f C, dot (vectorMap f l) B.rep = 0 := by
    intro B hB
    obtain ⟨B0, hB0, rfl⟩ := Finset.mem_image.mp hB
    exact (mapped_linezero_iff f l B0).mpr (hCline B0 hB0)
  have hXcard' : (imageSet f X).card = (imageSet f C).card := by
    rw [imageSet_card, imageSet_card]; exact hXcard
  have hYcard' : (imageSet f Y).card = (imageSet f C).card := by
    rw [imageSet_card, imageSet_card]; exact hYcard
  have hCnon' : (imageSet f C).Nonempty := Finset.card_pos.mp (by
    rw [imageSet_card]; exact Finset.card_pos.mpr hCnon)
  obtain ⟨Q, hQ, hQ0, hvan⟩ := BMMBlackLineConic.conic_of_collinear_matchings p
    (vectorMap f l) (mapped_line_nonzero f l hl) (imageSet f X) (imageSet f Y) (imageSet f C)
    (imageSet_disjoint f X Y hdisj) hXcard' hYcard' hCnon' (by rwa [imageSet_card])
    hXoff' hYoff' hCline' (image_collinear_matchings f X Y C hmatch)
  have hzero : ∀ P : ↥(X ∪ Y), eval (fun j => algebraMap R K (P.val.rep j)) Q = 0 := by
    intro P
    apply vanishing_on_image_implies_mapped_rep f Q hQ P.val
    apply hvan
    rcases Finset.mem_union.mp P.property with hPX | hPY
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨P.val, hPX, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨P.val, hPY, rfl⟩))
  obtain ⟨F, hF, hF0, hFvan⟩ := EquationScalarDescent.exists_equation_descent
    (fun P : ↥(X ∪ Y) => P.val.rep) 2 Q hQ hQ0 hzero
  exact ⟨F, hF, hF0, fun P hP => hFvan ⟨P, hP⟩⟩

end Cylinder.BMMBlackLineConicDescent

end
