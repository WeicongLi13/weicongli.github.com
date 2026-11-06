module

public import Cylinder.ManyTwoCharacter
public import Cylinder.ManyTwoArithmetic

/-! The many-two-point-rays lemma for literal components of the actual
minimum direction curve. All counting and numerical-character estimates
are derived from the original p-divisible configuration. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ManyTwoRays
open MvPolynomial
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition
open Cylinder.MinimumEquationComponentSets Cylinder.DirectionCurveComponentCounting
open Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.PlaneCurveFactors Cylinder.ManyTwoCharacter
variable (p : ℕ) [Fact p.Prime]

theorem many_two_on_component {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hsq : Squarefree F) (hG : G ∈ factors F)
    (hGirr : Irreducible (MvPolynomial.map (embedding p) G))
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F)
    (m : ℕ) (hm : 1 ≤ m) (hme : 4 * m + 2 < G.totalDegree)
    (hstair : ∀ j, 1 ≤ j → j ≤ m → j ≤ componentIncrement p hb s F G (3 * j)) :
    G.totalDegree * (5 * m + 2) <
      (twoPointDirections p hb (componentDirections p hb F G)).card := by
  have hcurve := direction_curve p hp hcard hS hnon hb s hs
  have hsupper := hcurve.2.1
  have he : G.totalDegree ≤ s := by
    have h := totalDegree_le_of_dvd_of_isDomain (factor_dvd F G hG) hF0
    rwa [hF.totalDegree hF0] at h
  obtain ⟨H, hFH⟩ := factor_dvd F G hG
  have hdegree := (hcomp G hG H hFH).2.2.2.2.2.2
  let δ := p - 2 * s
  have hpeq : p = 2 * s + δ := by dsimp only [δ]; omega
  have hδ : 3 ≤ δ := by dsimp only [δ]; omega
  have hδe : δ + 1 ≤ G.totalDegree := hdegree
  have hn : 2 * (whitePoints p S).card ≤ p * (p - 1) + 2 := by
    rw [SimpleBlackWeights.white_card_exact p hcard hS hnon]
    omega
  have hstaircase := component_staircase_bound p hb (by omega) s hsupper F G hF hF0
    hG hGirr hcomp m hme hstair
  have hcount := actual_two_point_component_excess_bound p hcard hS hb s F G hF hF0 hsq hG hcomp
  exact ManyTwoArithmetic.many_two_strict p s G.totalDegree δ m (componentExcess p hb s F G)
    (whitePoints p S).card (twoPointDirections p hb (componentDirections p hb F G)).card
    hpeq he hδe hδ hm hme hn hstaircase hcount

/-- The minimum curve, all its genuine component data, and the many-two-ray
conclusion are obtained solely from the original configuration. -/
theorem exists_many_two_curve {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ s : ℕ, ∃ F : MvPolynomial (Fin 3) (ZMod p),
      InitialDegree (representatives (embedding p) (directionSet p S b hb)) s ∧
      F.IsHomogeneous s ∧ F ≠ 0 ∧ (∀ P ∈ directionSet p S b hb, eval P.rep F = 0) ∧
      Squarefree F ∧ Squarefree (MvPolynomial.map (embedding p) F) ∧
      (∀ G ∈ factors F, Irreducible (MvPolynomial.map (embedding p) G)) ∧
      (∑ G ∈ factors F, G.totalDegree) = s ∧
      ComponentConclusion p s (directionSet p S b hb) F ∧
      ∀ G ∈ factors F, ∀ m : ℕ, 1 ≤ m → 4 * m + 2 < G.totalDegree →
        (∀ j, 1 ≤ j → j ≤ m → j ≤ componentIncrement p hb s F G (3 * j)) →
        G.totalDegree * (5 * m + 2) <
          (twoPointDirections p hb (componentDirections p hb F G)).card := by
  obtain ⟨s, hs, _hslow, _hsupper, _hklow, _hkwhite, _hkpolar, F, hF, hF0,
    hzero, hsq, hsqmap, habs, hsum, hcomp⟩ := exists_direction_curve p hp hcard hS hnon hb
  refine ⟨s, F, hs, hF, hF0, hzero, hsq, hsqmap, habs, hsum, hcomp, ?_⟩
  intro G hG m hm hme hstair
  exact many_two_on_component p hp hcard hS hnon hb s hs F G hF hF0 hsq hG (habs G hG)
    hcomp m hm hme hstair

end Cylinder.ManyTwoRays
end
