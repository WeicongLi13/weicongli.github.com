module

public import Cylinder.ManyTwoRays

/-! The actual two-point-ray subset inside the exclusive component index
type. Its cardinality equals the previously counted literal two-ray set. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ComponentTwoPointSubset
open MvPolynomial Finset
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition
open Cylinder.MinimumEquationComponents Cylinder.MinimumEquationComponentSets
open Cylinder.DirectionCurveComponentCounting Cylinder.RationalPlanePointModel
open Cylinder.PlaneBinaryReduction Cylinder.PlaneCurveFactors Cylinder.ManyTwoCharacter

theorem selected_subtype_card {A : Type*} [DecidableEq A] (D E : Finset A)
    (hED : E ⊆ D) (r : D → ℕ) :
    ((Finset.univ : Finset E).filter (fun P => r ⟨P.val, hED P.property⟩ = 2)).card =
      ((E.subtype (fun P => P ∈ D)).filter (fun i : D => r i = 2)).card := by
  classical
  apply Finset.card_bij (fun P _ => (⟨P.val, hED P.property⟩ : D))
  · intro P hP
    have hr := (mem_filter.mp hP).2
    exact mem_filter.mpr ⟨mem_subtype.mpr P.property, hr⟩
  · intro P _ Q _ h
    exact Subtype.ext (congrArg (fun i : D => i.val) h)
  · intro i hi
    have h := mem_filter.mp hi
    have hE : i.val ∈ E := mem_subtype.mp h.1
    let P : E := ⟨i.val, hE⟩
    refine ⟨P, mem_filter.mpr ⟨mem_univ _, ?_⟩, Subtype.ext rfl⟩
    exact h.2

variable (p : ℕ) [Fact p.Prime]

def componentIndex {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (P : exclusivePoints (directionSet p S b hb) H) : directionSet p S b hb :=
  ⟨P.val, exclusivePoints_subset (directionSet p S b hb) H P.property⟩

def twoPointSubset {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p)) :
    Finset (exclusivePoints (directionSet p S b hb) H) :=
  Finset.univ.filter (fun P => raySize p S b hb (componentIndex p hb H P) = 2)

@[simp] theorem mem_twoPointSubset {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : MvPolynomial (Fin 3) (ZMod p))
    (P : exclusivePoints (directionSet p S b hb) H) :
    P ∈ twoPointSubset p hb H ↔ raySize p S b hb (componentIndex p hb H P) = 2 := by
  simp [twoPointSubset]

theorem twoPointSubset_card {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (F G H : MvPolynomial (Fin 3) (ZMod p))
    (heq : exclusivePoints (directionSet p S b hb) H = componentPoints (directionSet p S b hb) F G) :
    (twoPointSubset p hb H).card = (twoPointDirections p hb (componentDirections p hb F G)).card := by
  unfold twoPointDirections componentDirections
  rw [← heq]
  exact selected_subtype_card (directionSet p S b hb)
    (exclusivePoints (directionSet p S b hb) H) (exclusivePoints_subset _ H) (raySize p S b hb)

theorem twoPointSubset_card_gt {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (s : ℕ)
    (hs : InitialDegree (representatives (embedding p) (directionSet p S b hb)) s)
    (F G H : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hsq : Squarefree F) (hG : G ∈ factors F)
    (hGirr : Irreducible (MvPolynomial.map (embedding p) G))
    (hcomp : ComponentConclusion p s (directionSet p S b hb) F) (hFH : F = G * H)
    (m : ℕ) (hm : 1 ≤ m) (hme : 4 * m + 2 < G.totalDegree)
    (hstair : ∀ j, 1 ≤ j → j ≤ m → j ≤ componentIncrement p hb s F G (3 * j)) :
    G.totalDegree * (5 * m + 2) < (twoPointSubset p hb H).card := by
  rw [twoPointSubset_card p hb F G H (hcomp G hG H hFH).1]
  exact ManyTwoRays.many_two_on_component p hp hcard hS hnon hb s hs F G hF hF0 hsq hG
    hGirr hcomp m hm hme hstair

end Cylinder.ComponentTwoPointSubset
end
