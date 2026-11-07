module

public import Cylinder.ManuscriptProjectionBounds
public import Cylinder.ProjectionTransportScalarExtension

/-! Lemma 6.4 on the actual exceptional rays of any prescribed chart. -/

@[expose] public section
noncomputable section
open scoped Classical
namespace Cylinder.ManuscriptExceptionalDirections
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.RationalPlanePointModel
open Cylinder.HilbertEvaluation Cylinder.EvaluationProjection
open Cylinder.ManuscriptProjectionBounds

variable (p : ℕ) [Fact p.Prime]

theorem independent (hp : 11 ≤ p) {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (C : ManuscriptProjectionBounds.ProjectionChart p b) :
    Function.Surjective (evaluationMap
      (fun i : ManuscriptProjectionBounds.largeRays p S b hb C =>
        representatives (embedding p) (directions p S b hb C) i.val) ((p - 5) / 2)) := by
  let e := largeIndexEquiv p S b hb C
  let v₀ := fun i : DirectionExcess.largeRays p S b hb =>
    representatives (embedding p) (directionSet p S b hb) i.val
  let v := fun i : ManuscriptProjectionBounds.largeRays p S b hb C =>
    representatives (embedding p) (directions p S b hb C) i.val
  have h₀ : Independent v₀ ((p - 5) / 2) := by
    intro w
    obtain ⟨F, hF⟩ := FinalExceptionalDirections.exceptional_directions_independent
      p hp hcard hS hnon hb w
    exact ⟨F.val, F.property, fun i => congrFun hF i⟩
  have hpre : Independent (fun i => v (e i)) ((p - 5) / 2) := by
    have h := (ProjectionTransportScalarExtension.independent_mapped_linearEquiv_rescaling
      (embedding p) C.directionEquiv
      (fun i : DirectionExcess.largeRays p S b hb => i.val.val.rep)
      (fun i => (ProjectionTransport.representativeScale (whiteImage p S)
        (black_outside_whiteImage p hb) C i.val : ZMod p))
      (fun i => (ProjectionTransport.representativeScale (whiteImage p S)
        (black_outside_whiteImage p hb) C i.val).ne_zero) ((p - 5) / 2)).mpr h₀
    convert h using 1
    funext i j
    change embedding p ((ProjectionTransport.indexEquiv (whiteImage p S)
      (black_outside_whiteImage p hb) C i.val).val.rep j) = _
    rw [ProjectionTransport.representativeScale_spec]
  have h : Independent v ((p - 5) / 2) := by
    have he := ProjectionTransport.independent_reindex e.symm v ((p - 5) / 2)
    exact he.mp hpre
  intro w
  obtain ⟨F, hF, hval⟩ := h w
  exact ⟨⟨F, hF⟩, funext hval⟩

theorem relation_space_eq_bot (hp : 11 ≤ p) {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (C : ManuscriptProjectionBounds.ProjectionChart p b) :
    PlaneRelationSpaces.relationSpace
      (fun i : ManuscriptProjectionBounds.largeRays p S b hb C =>
        representatives (embedding p) (directions p S b hb C) i.val) ((p - 5) / 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  rw [Submodule.mem_bot]
  apply funext
  exact GapRelations.relation_zero_of_surjective _ c _
    (independent p hp hcard hS hnon hb C)
    ((PlaneRelationSpaces.mem_relationSpace _ _ c).mp hc)

end Cylinder.ManuscriptExceptionalDirections
end
