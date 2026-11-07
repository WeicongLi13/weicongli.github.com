module

public import Cylinder.ArbitraryMoments

/-! Scalar extension and prescribed components for the moments of the actual
preassigned plane equations, in the actual preassigned projection chart. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ArbitraryMomentPrescribed
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.ProjectionChart Cylinder.EvaluationProjection
open Cylinder.ExactRayMomentsCanonicalTimes Cylinder.ProductRescaling
open Cylinder.ArbitraryMomentData Cylinder.ArbitraryMoments

variable (p : ℕ) [Fact p.Prime]
variable {S : Finset (Geometry.Point p)} {b : DualPoint p}

theorem all_moment_relations {K : Type*} [Field K] (ι : ZMod p →+* K)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (v : directionSet p S b hb → Fin 3 → ZMod p) (hv : ∀ i, v i ≠ 0)
    (hpoint : ∀ i, Projectivization.mk (ZMod p) (v i) (hv i) =
      (ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C i).val)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = v i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p a E ^ (p - 2)) = 0) (j : ℕ) (hj : j ≤ p - 2) :
    PowerEvaluationRelation.Relation (fun i k => ι (v i k))
      (fun i => ι (prescribedMoment p C hb a c i j)) (p - 2 - j) := by
  have hs (i : directionSet p S b hb) :
      ∃ u : (ZMod p)ˣ, v i = (u : ZMod p) • C.directionEquiv i.val.rep :=
    ProjectionTransport.arbitrary_representative_scale (whiteImage p S)
      (black_outside_whiteImage p hb) C i (v i) (hv i) (hpoint i)
  let lam : directionSet p S b hb → (ZMod p)ˣ := fun i => Classical.choose (hs i)
  have hdir : v = direction p C hb lam := funext (fun i => Classical.choose_spec (hs i))
  have hnorm' : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i := by
    simpa only [hdir] using hnorm
  obtain ⟨β, hβ⟩ := planeScale_exhaustive p C hb lam a ha hnorm'
  rw [← hβ] at hprod hpower
  have h := all_moment_relations_over_field p ι C hb lam β c hc hprod hpower j hj
  have hm (i : directionSet p S b hb) :
      (∑ ν : Fin (raySize p S b hb i), ι (c (rayWhitePoint p hb i ν).val) *
        ι (time p C hb lam i ν) ^ j) = ι (prescribedMoment p C hb a c i j) := by
    rw [prescribedMoment_eq p C hb lam a c hnorm' i j]
    simp only [actualMoment, map_sum, map_mul, map_pow]
  simpa only [← hdir, hm] using h

/-- The cofactor may be any preassigned polynomial over the curve field.
For a specified minimum equation F=G*H, this is precisely its exclusive
component set H≠0.  The same global forms work on every such set. -/
theorem component_moments {K : Type*} [Field K] (ι : ZMod p →+* K)
    (hp : 11 ≤ p) (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (C : Chart (coordinatePoint p b))
    (hb : b ∈ blackPoints p S)
    (v : directionSet p S b hb → Fin 3 → ZMod p) (hv : ∀ i, v i ≠ 0)
    (hpoint : ∀ i, Projectivization.mk (ZMod p) (v i) (hv i) =
      (ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C i).val)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = v i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p a E ^ (p - 2)) = 0)
    (H : MvPolynomial (Fin 3) K) :
    ∃ f g : MvPolynomial (Fin 3) K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      ∀ i, eval (fun k => ι (v i k)) H ≠ 0 →
        ι (prescribedMoment p C hb a c i 2) = eval (fun k => ι (v i k)) f *
          ι (prescribedMoment p C hb a c i 1) ∧
        ι (prescribedMoment p C hb a c i 3) = eval (fun k => ι (v i k)) g *
          ι (prescribedMoment p C hb a c i 1) := by
  obtain ⟨_, _, _, ⟨⟨f, g⟩, ⟨hf, hg, hfv, hgv⟩, _⟩⟩ := prescribed_representatives p hp hcard hS
    hnon C hb v hv hpoint a c ha hnorm hc hprod hpower
  refine ⟨MvPolynomial.map ι f, MvPolynomial.map ι g, hf.map ι, hg.map ι, ?_⟩
  intro i _
  constructor
  · rw [FrobeniusPolarBound.eval_map_at_mapped_point, ← map_mul, hfv i]
  · rw [FrobeniusPolarBound.eval_map_at_mapped_point, ← map_mul, hgv i]

#print axioms all_moment_relations
#print axioms component_moments

end Cylinder.ArbitraryMomentPrescribed
end
