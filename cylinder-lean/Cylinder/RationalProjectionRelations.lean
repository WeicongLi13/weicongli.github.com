module

public import Cylinder.ProjectiveVandermonde
public import Cylinder.ProjectiveFieldEmbedding
public import Cylinder.RationalPlanePointModel

/-! A rational coordinate change and rational ray normalization preserve
relations with arbitrary extension-field coefficients. The coefficients
need not lie in the prime field. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.RationalProjectionRelations
open MvPolynomial Cylinder.LinearEvaluationTransport Cylinder.ProjectiveFieldEmbedding
open Cylinder.ProjectiveProjection Cylinder.EvaluationProjection

section Change
variable {R K σ J : Type*} [Field R] [Field K] [Fintype σ]

def rationalPullback (f : R →+* K) (g : (σ → R) ≃ₗ[R] (σ → R)) (P : MvPolynomial σ K) :
    MvPolynomial σ K := aeval (fun j => MvPolynomial.map f (linearCoordinate g j)) P

theorem rationalPullback_homogeneous (f : R →+* K) (g : (σ → R) ≃ₗ[R] (σ → R))
    (P : MvPolynomial σ K) (d : ℕ) (hP : P.IsHomogeneous d) :
    (rationalPullback f g P).IsHomogeneous d := by
  simpa only [rationalPullback, one_mul] using hP.aeval
    (fun j => MvPolynomial.map f (linearCoordinate g j))
      (fun j => (linearCoordinate_homogeneous g j).map f)

theorem rationalPullback_eval (f : R →+* K) (g : (σ → R) ≃ₗ[R] (σ → R))
    (P : MvPolynomial σ K) (x : σ → R) :
    eval (vectorMap f x) (rationalPullback f g P) = eval (vectorMap f (g x)) P := by
  change aeval (vectorMap f x) (aeval (fun j => MvPolynomial.map f (linearCoordinate g j)) P) = _
  rw [comp_aeval_apply]
  have hvalues : (fun j => aeval (vectorMap f x) (MvPolynomial.map f (linearCoordinate g j))) =
      vectorMap f (g x) := by
    funext j
    change eval (fun i => f (x i)) (MvPolynomial.map f (linearCoordinate g j)) = f (g x j)
    exact (MvPolynomial.map_eval f x (linearCoordinate g j)).symm.trans
      (congrArg f (linearCoordinate_eval g j x))
  rw [hvalues]
  rfl

theorem relation_after_rational_change [Fintype J] (f : R →+* K)
    (g : (σ → R) ≃ₗ[R] (σ → R)) (x : J → σ → R) (c : J → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation (fun i => vectorMap f (x i)) c d) :
    PowerEvaluationRelation.Relation (fun i => vectorMap f (g (x i))) c d := by
  intro P hP
  simpa only [rationalPullback_eval] using hrel (rationalPullback f g P)
    (rationalPullback_homogeneous f g P d hP)

end Change

section Projection
variable {R K σ : Type*} [Field R] [Field K] [Fintype σ]
variable (f : R →+* K) (E : Finset (ProjectiveProjection.Point R σ))
variable (centre : ProjectiveProjection.Point R σ) (hout : centre ∉ E)

def directionRepresentatives : directionSet R σ E centre hout → σ → K :=
  fun i => vectorMap f i.val.rep

def rayParameters : ∀ i : directionSet R σ E centre hout, Fin (raySize R σ E centre hout i) → K :=
  fun i ν => f (rayTimes R σ E centre hout i ν)

def normalizedResidues (c : E → K) (d : ℕ)
    (i : directionSet R σ E centre hout) (ν : Fin (raySize R σ E centre hout i)) : K :=
  c (rayEnumeration R σ E centre hout i ν).val /
    f (normalisingUnit R σ E centre hout i (rayEnumeration R σ E centre hout i ν) : R) ^ d

theorem normalizedResidues_ne_zero (c : E → K) (hc : ∀ x, c x ≠ 0) (d : ℕ) :
    ∀ i ν, normalizedResidues f E centre hout c d i ν ≠ 0 := by
  intro i ν
  apply div_ne_zero (hc _)
  apply pow_ne_zero
  exact fun hz => Units.ne_zero _ ((map_eq_zero_iff f f.injective).mp hz)

theorem rayParameters_injective : ∀ i, Function.Injective (rayParameters f E centre hout i) :=
  fun i => f.injective.comp (rayTimes_injective R σ E centre hout i)

set_option maxHeartbeats 800000 in
theorem sum_over_rational_rays (w : E → K) :
    (∑ i : directionSet R σ E centre hout, ∑ ν : Fin (raySize R σ E centre hout i),
      w (rayEnumeration R σ E centre hout i ν).val) = ∑ x : E, w x := by
  calc
    _ = ∑ i : directionSet R σ E centre hout, ∑ x : RayIndex R σ E centre hout i, w x.val := by
      apply Finset.sum_congr rfl
      intro i _
      exact (rayEnumeration R σ E centre hout i).sum_comp (fun x => w x.val)
    _ = ∑ x : (Σ i : directionSet R σ E centre hout, RayIndex R σ E centre hout i), w x.2.val :=
      (Fintype.sum_sigma (fun x : (Σ i : directionSet R σ E centre hout,
        RayIndex R σ E centre hout i) => w x.2.val)).symm
    _ = ∑ x : E, w x := (Equiv.sigmaFiberEquiv (projectionIndex R σ E centre hout)).sum_comp w

theorem normalized_evaluation_relation (c : E → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation (fun x : E => vectorMap f x.val.rep) c d) :
    EvaluationRelation (directionRepresentatives f E centre hout) (raySize R σ E centre hout)
      (rayParameters f E centre hout) (normalizedResidues f E centre hout c d) d := by
  intro P hP
  have hlinear := relation_after_rational_change f (coordinateChange R σ centre)
    (fun x : E => x.val.rep) c d hrel
  calc
    (∑ i : directionSet R σ E centre hout, ∑ ν : Fin (raySize R σ E centre hout i),
      normalizedResidues f E centre hout c d i ν *
        eval (rayPoint (directionRepresentatives f E centre hout i) (rayParameters f E centre hout i ν)) P) =
      ∑ i : directionSet R σ E centre hout, ∑ ν : Fin (raySize R σ E centre hout i),
        c (rayEnumeration R σ E centre hout i ν).val *
          eval (vectorMap f (coordinateChange R σ centre (rayEnumeration R σ E centre hout i ν).val.val.rep)) P := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro ν _
      let x := rayEnumeration R σ E centre hout i ν
      let u := normalisingUnit R σ E centre hout i x
      have hnorm := congrArg (vectorMap f) (normalizedVector_eq_rayPoint R σ E centre hout i x)
      have hnorm' : f (u : R) • vectorMap f (coordinateChange R σ centre x.val.val.rep) =
          rayPoint (directionRepresentatives f E centre hout i) (rayParameters f E centre hout i ν) := by
        change vectorMap f ((u : R) • coordinateChange R σ centre x.val.val.rep) = _ at hnorm
        have hs : vectorMap f ((u : R) • coordinateChange R σ centre x.val.val.rep) =
            f (u : R) • vectorMap f (coordinateChange R σ centre x.val.val.rep) := by
          funext j
          exact f.map_mul _ _
        rw [hs] at hnorm
        have hp : vectorMap f (rayPoint i.val.rep (rayParameter R σ E centre hout i x)) =
            rayPoint (directionRepresentatives f E centre hout i) (rayParameters f E centre hout i ν) := by
          funext j
          cases j <;> rfl
        rw [hp] at hnorm
        exact hnorm
      change (c x.val / f (u : R) ^ d) *
        eval (rayPoint (directionRepresentatives f E centre hout i) (rayParameters f E centre hout i ν)) P = _
      rw [← hnorm', homogeneous_eval_smul P d hP, ← mul_assoc]
      have hu : f (u : R) ≠ 0 := fun hz => Units.ne_zero u ((map_eq_zero_iff f f.injective).mp hz)
      rw [div_mul_cancel₀ _ (pow_ne_zero d hu)]
    _ = ∑ x : E, c x * eval (vectorMap f (coordinateChange R σ centre x.val.rep)) P :=
      sum_over_rational_rays E centre hout
        (fun x => c x * eval (vectorMap f (coordinateChange R σ centre x.val.rep)) P)
    _ = 0 := hlinear P hP

theorem ray_lower_bound_of_independent [Infinite K] (c : E → K) (hc : ∀ x, c x ≠ 0)
    (d a : ℕ) (ha : a ≤ d)
    (hrel : PowerEvaluationRelation.Relation (fun x : E => vectorMap f x.val.rep) c d)
    (hind : Independent (directionRepresentatives f E centre hout) a) :
    ∀ i : directionSet R σ E centre hout, d - a + 2 ≤ raySize R σ E centre hout i := by
  apply ray_size_lower_bound_of_evaluation_relation (directionRepresentatives f E centre hout)
    (fun i hz => i.val.rep_nonzero ((vectorMap_injective f) (by
      simpa only [directionRepresentatives, vectorMap, map_zero, Pi.zero_apply] using hz)))
    (raySize R σ E centre hout) (raySize_pos R σ E centre hout)
    (rayParameters f E centre hout) (normalizedResidues f E centre hout c d)
    (rayParameters_injective f E centre hout) (normalizedResidues_ne_zero f E centre hout c hc d)
    d a ha hind (normalized_evaluation_relation f E centre hout c d hrel)

end Projection

#print axioms rationalPullback_homogeneous
#print axioms rationalPullback_eval
#print axioms relation_after_rational_change
#print axioms normalized_evaluation_relation
#print axioms ray_lower_bound_of_independent

end Cylinder.RationalProjectionRelations
end
