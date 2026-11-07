module
public import Cylinder.MomentProductActual
public import Cylinder.ArbitraryMomentPrescribed
/-! Final fixed-data moment interfaces with the polynomial identities written
in the prescribed projection coordinates themselves. -/
@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ManuscriptMomentTheorems
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.ProjectionChart Cylinder.EvaluationProjection
open Cylinder.ExactRayMomentsCanonicalTimes Cylinder.ProductRescaling
open Cylinder.ArbitraryMomentData
variable (p : ℕ) [Fact p.Prime]
variable {S : Finset (Geometry.Point p)} {b : DualPoint p}
theorem exact_and_global_moments (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (v : directionSet p S b hb → Fin 3 → ZMod p) (hv : ∀ i, v i ≠ 0)
    (hpoint : ∀ i, Projectivization.mk (ZMod p) (v i) (hv i) =
      (ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C i).val)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = v i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, MomentProductCoordinates.factor p C a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
        ∏ H ∈ (whitePoints p S).erase E, MomentProductCoordinates.factor p C a H)
    (hpower : (∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
      MomentProductCoordinates.factor p C a E ^ (p - 2)) = 0) :
    (∀ i, prescribedMoment p C hb a c i 0 = 0) ∧
    (∀ i, prescribedMoment p C hb a c i 1 ≠ 0) ∧
    PowerEvaluationRelation.Relation v (fun i => prescribedMoment p C hb a c i 1) (p - 3) ∧
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ i, prescribedMoment p C hb a c i 2 = eval (v i) fg.1 * prescribedMoment p C hb a c i 1) ∧
      (∀ i, prescribedMoment p C hb a c i 3 = eval (v i) fg.2 * prescribedMoment p C hb a c i 1) := by
  exact ArbitraryMoments.prescribed_representatives p hp hcard hS hnon C hb v hv hpoint a c ha hnorm hc
    ((MomentProductCoordinates.product_identity_iff p S C a c).mpr hprod)
    ((MomentProductCoordinates.power_identity_iff p S C a c).mpr hpower)

theorem all_moment_relations {K : Type*} [Field K] (ι : ZMod p →+* K)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (v : directionSet p S b hb → Fin 3 → ZMod p) (hv : ∀ i, v i ≠ 0)
    (hpoint : ∀ i, Projectivization.mk (ZMod p) (v i) (hv i) =
      (ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C i).val)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = v i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, MomentProductCoordinates.factor p C a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
        ∏ H ∈ (whitePoints p S).erase E, MomentProductCoordinates.factor p C a H)
    (hpower : (∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
      MomentProductCoordinates.factor p C a E ^ (p - 2)) = 0) (j : ℕ) (hj : j ≤ p - 2) :
    PowerEvaluationRelation.Relation (fun i k => ι (v i k))
      (fun i => ι (prescribedMoment p C hb a c i j)) (p - 2 - j) := by
  exact ArbitraryMomentPrescribed.all_moment_relations p ι C hb v hv hpoint a c ha hnorm hc
    ((MomentProductCoordinates.product_identity_iff p S C a c).mpr hprod)
    ((MomentProductCoordinates.power_identity_iff p S C a c).mpr hpower) j hj

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
    (hprod : (∏ H ∈ blackPoints p S, MomentProductCoordinates.factor p C a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
        ∏ H ∈ (whitePoints p S).erase E, MomentProductCoordinates.factor p C a H)
    (hpower : (∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
      MomentProductCoordinates.factor p C a E ^ (p - 2)) = 0)
    (H : MvPolynomial (Fin 3) K) :
    ∃ f g : MvPolynomial (Fin 3) K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      ∀ i, eval (fun k => ι (v i k)) H ≠ 0 →
        ι (prescribedMoment p C hb a c i 2) = eval (fun k => ι (v i k)) f *
          ι (prescribedMoment p C hb a c i 1) ∧
        ι (prescribedMoment p C hb a c i 3) = eval (fun k => ι (v i k)) g *
          ι (prescribedMoment p C hb a c i 1) := by
  exact ArbitraryMomentPrescribed.component_moments p ι hp hcard hS hnon C hb v hv hpoint a c ha hnorm hc
    ((MomentProductCoordinates.product_identity_iff p S C a c).mpr hprod)
    ((MomentProductCoordinates.power_identity_iff p S C a c).mpr hpower) H

#print axioms exact_and_global_moments
#print axioms all_moment_relations
#print axioms component_moments
end Cylinder.ManuscriptMomentTheorems
end
