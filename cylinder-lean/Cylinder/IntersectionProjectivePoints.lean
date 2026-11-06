module

public import Cylinder.IntersectionArtinBridge
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Actual finite projective point sets supply distinct nonzero representatives. -/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionProjectivePoints

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.IntersectionZeroSet Cylinder.IntersectionBinaryGeneration Cylinder.IntersectionArtinBridge
open scoped Classical LinearAlgebra.Projectivization

variable {K I : Type*} [Field K] [Fintype I] [Nonempty I]

abbrev PlanePoint := Projectivization K (Fin 3 → K)

def representatives (T : Finset (PlanePoint (K := K))) : T → Fin 3 → K := fun x => x.val.rep

theorem representatives_nonzero (T : Finset (PlanePoint (K := K))) :
    ∀ x : T, representatives T x ≠ 0 := fun x => x.val.rep_nonzero

theorem representatives_distinct (T : Finset (PlanePoint (K := K))) :
    ProjectivelyDistinct (representatives T) := by
  intro x y hxy c heq
  have hyx : y.val = x.val := by
    have h := (Projectivization.mk_eq_mk_iff' K y.val.rep x.val.rep
      y.val.rep_nonzero x.val.rep_nonzero).mpr ⟨c, heq.symm⟩
    simpa only [Projectivization.mk_rep] using h
  exact hxy (Subtype.ext hyx.symm)

theorem independent_projective_intersections_on_graph [Infinite K]
    (F : I → PlaneRing K) (e : I → ℕ) (he : ∀ i, 0 < e i)
    (hhom : ∀ i, (F i).IsHomogeneous (e i))
    (T : Finset (PlanePoint (K := K)))
    (hT : ∀ x : T, OnMultipleComponents F x.val.rep)
    (a b : K) (havoid : ∀ x : T, eval x.val.rep (graphEquation a b) ≠ 0)
    (hR0 : ∀ i, graphRestriction a b (F i) ≠ 0)
    (hRcop : Pairwise (fun i j => IsRelPrime (graphRestriction a b (F i)) (graphRestriction a b (F j))))
    (d : ℕ) (hd : degreeSum e - 2 ≤ d) : EvaluationProjection.Independent (representatives T) d :=
  independent_intersections_on_graph F e he hhom (representatives T)
    (representatives_nonzero T) (representatives_distinct T) hT a b havoid hR0 hRcop d hd

#print axioms representatives_distinct
#print axioms independent_projective_intersections_on_graph

end Cylinder.IntersectionProjectivePoints

end
