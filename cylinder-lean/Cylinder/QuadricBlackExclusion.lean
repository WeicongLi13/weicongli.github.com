module

public import Cylinder.QuadricProjectionRestriction
public import Cylinder.DirectionCurveProposition
public import Cylinder.EquationScalarDescent

/-! A genuine quadric through every actual white dual point cannot contain
an actual black dual point. Coefficient descent and the actual projection
give the forbidden low-degree direction equation. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.QuadricBlackExclusion

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductEvaluationRelation Cylinder.BlackProjection
open Cylinder.ProjectiveProjection Cylinder.BlackProjectionVandermonde
open Cylinder.LinearEvaluationTransport Cylinder.PlaneBinaryReduction
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.EquationScalarDescent
open Cylinder.RationalPlanePointModel Cylinder.DirectionCurveBounds

variable (p : ℕ) [Fact p.Prime]

theorem no_small_direction_equation {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (d : ℕ) (hd : d ≤ 2)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hzero : ∀ i : directionSet p S b hb, eval i.val.rep F = 0) : False := by
  obtain ⟨s, hs, hlo, _⟩ := DirectionCurveProposition.exists_direction_curve p hp hcard hS hnon hb
  have hsd : d < s := by unfold DirectionExcess.threshold at hlo; omega
  have hmap : (MvPolynomial.map (embedding p) F).IsHomogeneous d := hF.map _
  have hmap0 : MvPolynomial.map (embedding p) F ≠ 0 := by
    intro hz
    exact hF0 (MvPolynomial.map_injective (embedding p) (embedding p).injective
      (by simpa only [map_zero] using hz))
  have hpiece : idealPiece (representatives (embedding p) (directionSet p S b hb)) d ≠ ⊥ := by
    apply (idealPiece_ne_bot_iff _ _).mpr
    refine ⟨MvPolynomial.map (embedding p) F, hmap, hmap0, ?_⟩
    intro i
    change eval (fun j => embedding p (i.val.rep j)) (MvPolynomial.map (embedding p) F) = 0
    rw [FrobeniusPolarBound.eval_map_at_mapped_point, hzero i, map_zero]
  exact hpiece (hs.2 d hsd)

theorem reindexed_quadric_eval (Q : MvPolynomial (Fin 4) (ZMod p)) (H : DualPoint p) :
    eval (dualCoordinates p H.rep) (rename (finSuccEquiv 3) Q) = eval (coefficientVector p H) Q := by
  rw [eval_rename]
  simp only [dualCoordinates_coefficientVector, Function.comp_def, Equiv.symm_apply_apply]

theorem reindexed_quadric_eval_coordinatePoint (Q : MvPolynomial (Fin 4) (ZMod p))
    (hQ : Q.IsHomogeneous 2) (H : DualPoint p) (hzero : eval (coefficientVector p H) Q = 0) :
    eval (coordinatePoint p H).rep (rename (finSuccEquiv 3) Q) = 0 := by
  obtain ⟨u, hu⟩ := ExactRayMomentsCoordinates.exists_coordinate_rep_unit p H
  rw [← hu, Units.smul_def]
  rw [homogeneous_eval_smul _ 2 (hQ.rename_isHomogeneous (f := finSuccEquiv 3)),
    reindexed_quadric_eval, hzero, mul_zero]

theorem black_not_on_quadric_prime_field {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Q : MvPolynomial (Fin 4) (ZMod p)) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hwhite : ∀ H ∈ whitePoints p S, eval (coefficientVector p H) Q = 0)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) : eval (coefficientVector p b) Q ≠ 0 := by
  intro hblack
  let R := rename (finSuccEquiv 3) Q
  have hR : R.IsHomogeneous 2 := hQ.rename_isHomogeneous (f := finSuccEquiv 3)
  have hR0 : R ≠ 0 := by
    intro hz
    exact hQ0 ((rename_injective (finSuccEquiv 3) (finSuccEquiv 3).injective)
      (by simpa only [R, map_zero] using hz))
  have hcentre : eval (coordinatePoint p b).rep R = 0 :=
    reindexed_quadric_eval_coordinatePoint p Q hQ b hblack
  have hzero : ∀ P ∈ whiteImage p S, eval P.rep R = 0 := by
    intro P hP
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hP
    exact reindexed_quadric_eval_coordinatePoint p Q hQ H (hwhite H hH)
  obtain ⟨d, hd, F, hF, hF0, hvan⟩ := QuadricProjectionRestriction.quadric_directions_equation
    (whiteImage p S) (coordinatePoint p b) (black_outside_whiteImage p hb) R hR hR0
    (by simpa only [ZMod.card] using (show 2 < p by omega)) hcentre hzero
    (fun i => two_le_raySize p hcard hS hb i)
  exact no_small_direction_equation p hp hcard hS hnon hb d (by rcases hd with rfl | rfl <;> omega)
    F hF hF0 hvan

theorem black_not_on_quadric {K : Type*} [Field K] [Algebra (ZMod p) K]
    {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hwhite : ∀ H ∈ whitePoints p S,
      eval (fun j => algebraMap (ZMod p) K (coefficientVector p H j)) Q = 0)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    eval (fun j => algebraMap (ZMod p) K (coefficientVector p b j)) Q ≠ 0 := by
  intro hblack
  let v : (whitePoints p S ⊕ Unit) → Fin 4 → ZMod p :=
    Sum.elim (fun H => coefficientVector p H.val) (fun _ => coefficientVector p b)
  have hvan : ∀ i, eval (fun j => algebraMap (ZMod p) K (v i j)) Q = 0 := by
    intro i
    cases i with
    | inl H => exact hwhite H.val H.property
    | inr u => exact hblack
  obtain ⟨F, hF, hF0, hz⟩ := exists_equation_descent v 2 Q hQ hQ0 hvan
  have hFw : ∀ H ∈ whitePoints p S, eval (coefficientVector p H) F = 0 := by
    intro H hH
    exact hz (Sum.inl ⟨H, hH⟩)
  exact black_not_on_quadric_prime_field p hp hcard hS hnon F hF hF0 hFw hb (hz (Sum.inr ()))

end Cylinder.QuadricBlackExclusion

end
