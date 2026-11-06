module

public import Cylinder.BlackProjectionVandermonde

/-! Direction moment relations derived from the actual normalized white relation. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.RayMomentRelations

open Cylinder.EvaluationProjection Cylinder.BlackProjection Cylinder.ProjectiveBalance
open Cylinder.ProjectiveGeometry

variable {K σ I : Type*} [Field K] [Fintype I]

theorem relation_of_moments (v : I → σ → K) (r : I → ℕ)
    (t c : ∀ i, Fin (r i) → K) (d j : ℕ) (hj : j ≤ d)
    (hrel : EvaluationRelation v r t c d) :
    PowerEvaluationRelation.Relation v (fun i => rayMoment r t c i j) (d - j) :=
  fun G hG => moment_evaluation_relation v r t c d j hj hrel G hG

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem actual_black_moment_relations {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : ∀ i : directionSet p S b hb, Fin (raySize p S b hb i) → K,
      (∀ i ν, c i ν ≠ 0) ∧
      EvaluationRelation (BlackProjectionVandermonde.directionRepresentatives p hb)
        (raySize p S b hb) (BlackProjectionVandermonde.rayTimesOverField p hb) c (p - 2) ∧
      ∀ j, j ≤ p - 2 → PowerEvaluationRelation.Relation
        (BlackProjectionVandermonde.directionRepresentatives p hb)
        (fun i => rayMoment (raySize p S b hb)
          (BlackProjectionVandermonde.rayTimesOverField p hb) c i j) (p - 2 - j) := by
  obtain ⟨c, hc, hrel⟩ :=
    BlackProjectionVandermonde.exists_normalized_relation_over_field p (K := K) hcard hS hb
  exact ⟨c, hc, hrel, fun j hj => relation_of_moments _ _ _ _ _ _ hj hrel⟩

end Cylinder.RayMomentRelations

end
