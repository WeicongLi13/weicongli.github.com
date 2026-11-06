module

public import Cylinder.GlobalMomentsFromComponents

/-! The global argument uses the same actual product residues as the
component argument. All three relation degrees follow from that one
actual ray evaluation relation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentResidues

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition Cylinder.PlaneCurveFactors
open Cylinder.MinimumEquationComponentSets Cylinder.ExactRayMomentsTheorem
open Cylinder.BlackProjectionVandermonde Cylinder.EvaluationProjection

variable (p : ℕ) [Fact p.Prime]

abbrev actualMoment {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (P : directionSet p S b hb) (j : ℕ) : CurveField p :=
  rayMoment (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) P j

theorem actual_moment_relation {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
      (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (j : ℕ) (hj : j ≤ p - 2) :
    PowerEvaluationRelation.Relation (representatives (embedding p) (directionSet p S b hb))
      (fun P => actualMoment p hb c P j) (p - 2 - j) := by
  have hm := RayMomentRelations.relation_of_moments _ _ _ _ (p - 2) j hj hrel
  have hreps : directionRepresentatives p (K := CurveField p) hb =
      representatives (embedding p) (directionSet p S b hb) := by
    funext P i
    exact congrArg (fun f : ZMod p →+* CurveField p => f (P.val.rep i))
      (Subsingleton.elim (ProductEvaluationRelation.primeEmbedding p) (embedding p))
  rw [hreps] at hm
  exact hm

theorem first_three_actual_relations {S : Finset (Geometry.Point p)} (hp : 5 ≤ p)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
      (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2)) :
    PowerEvaluationRelation.Relation (representatives (embedding p) (directionSet p S b hb))
      (fun P => actualMoment p hb c P 1) (p - 3) ∧
    PowerEvaluationRelation.Relation (representatives (embedding p) (directionSet p S b hb))
      (fun P => actualMoment p hb c P 2) (p - 4) ∧
    PowerEvaluationRelation.Relation (representatives (embedding p) (directionSet p S b hb))
      (fun P => actualMoment p hb c P 3) (p - 5) := by
  exact ⟨by simpa only [Nat.sub_sub, Nat.reduceAdd] using
    actual_moment_relation p hb c hrel 1 (by omega),
    by simpa only [Nat.sub_sub, Nat.reduceAdd] using actual_moment_relation p hb c hrel 2 (by omega),
    by simpa only [Nat.sub_sub, Nat.reduceAdd] using actual_moment_relation p hb c hrel 3 (by omega)⟩

set_option maxHeartbeats 800000 in
theorem global_actual_moments_given_component_forms {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (s : ℕ) (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (hsq : Squarefree F) (hzero : ∀ P ∈ directionSet p S b hb, eval P.rep F = 0)
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (c : DualPoint p → ZMod p)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
      (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (hfirst : ∀ P, actualMoment p hb c P 1 ≠ 0)
    (fi gi : factors F → MvPolynomial (Fin 3) (CurveField p))
    (hfi : ∀ G, (fi G).IsHomogeneous 1) (hgi : ∀ G, (gi G).IsHomogeneous 2)
    (hidf : ∀ G : factors F, ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G.val →
        actualMoment p hb c P 2 = eval (representatives (embedding p) (directionSet p S b hb) P) (fi G) *
          actualMoment p hb c P 1)
    (hidg : ∀ G : factors F, ∀ P : directionSet p S b hb,
      P.val ∈ componentPoints (directionSet p S b hb) F G.val →
        actualMoment p hb c P 3 = eval (representatives (embedding p) (directionSet p S b hb) P) (gi G) *
          actualMoment p hb c P 1) :
    ∃ f g : MvPolynomial (Fin 3) (CurveField p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ G, fi G = f) ∧ (∀ G, gi G = g) ∧
      (∀ P : directionSet p S b hb,
        actualMoment p hb c P 2 = eval (representatives (embedding p) (directionSet p S b hb) P) f *
          actualMoment p hb c P 1) ∧
      ∀ P : directionSet p S b hb,
        actualMoment p hb c P 3 = eval (representatives (embedding p) (directionSet p S b hb) P) g *
          actualMoment p hb c P 1 := by
  obtain ⟨h1, h2, h3⟩ := first_three_actual_relations p (by omega) hb c hrel
  exact GlobalMomentsFromComponents.global_moment_forms_from_components p hp hcard hS hnon hb s hs
    F hF hF0 hsq hzero hcomp (fun P => actualMoment p hb c P 1)
    (fun P => actualMoment p hb c P 2) (fun P => actualMoment p hb c P 3) hfirst h1 h2 h3 fi gi hfi hgi hidf hidg

end Cylinder.GlobalMomentResidues

end
