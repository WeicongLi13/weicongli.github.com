module

public import Cylinder.GraphPlaneLine

/-!
# Simultaneous graph-line gcd preservation

Every gcd, residual quotient, coprime pair, and line below is constructed from
the actual finite homogeneous generator families. This is the line-selection
step of the plane plateau proof. It does not assert the remaining scheme/colon
or Hilbert-dimension bridge for an arbitrary saturated nonreduced scheme.
-/

@[expose] public section
noncomputable section
namespace Cylinder.GcdGraphSelection
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.GenericPlaneLine Cylinder.PrimitivePlaneSystem
open Cylinder.GcdPlaneLine Cylinder.GraphPlaneLine
variable {K J T : Type*} [Field K] [Infinite K] [Fintype J] [Fintype T]

/-- One actual graph line preserves the gcd and its degree for every generator
system at once, and avoids a prescribed finite projective support. -/
theorem exists_graph_preserving_gcds_avoiding
    (I : J → Type*) [∀ j, Fintype (I j)] (f : ∀ j, I j → PlaneRing K) (d : J → ℕ)
    (hhom : ∀ j i, (f j i).IsHomogeneous (d j)) (hf : ∀ j, ∃ i, f j i ≠ 0)
    (v : T → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : K, (∀ i, eval (v i) (graphEquation a b) ≠ 0) ∧
      ∀ j, graphRestriction a b (familyGcd (f j)) ≠ 0 ∧
        (graphRestriction a b (familyGcd (f j))).totalDegree = (familyGcd (f j)).totalDegree ∧
          ∀ D : BinaryRing K,
            (∀ i, D ∣ graphRestriction a b (f j i)) ↔ D ∣ graphRestriction a b (familyGcd (f j)) := by
  classical
  let U (j : J) := Submodule.span K (Set.range (residualFamily (f j)))
  have hU (j : J) : U j ≠ ⊥ := residual_span_ne_zero (f j) (hf j)
  have hhomU (j : J) : U j ≤ Forms K (d j - (familyGcd (f j)).totalDegree) :=
    residual_span_homogeneous (f j) (d j) (hhom j) (hf j)
  choose F hFU G hGU hF0 hcop using fun j : J =>
    exists_relPrime_pair (U j) (hU j) (residual_primitive (f j) (hf j))
  obtain ⟨a, b, hpair, havoid, hH0⟩ := exists_graph_coprime_avoiding_with_nonzero F G
    (fun j => d j - (familyGcd (f j)).totalDegree) (fun j => d j - (familyGcd (f j)).totalDegree)
    (fun j => hhomU j (hFU j)) (fun j => hhomU j (hGU j)) hF0 hcop v hv
    (fun j => familyGcd (f j)) (fun j => familyGcd_ne_zero (f j) (hf j))
  refine ⟨a, b, havoid, ?_⟩
  intro j
  refine ⟨hH0 j, (graphRestriction_homogeneous a b _ _
    (familyGcd_homogeneous (f j) (d j) (hhom j) (hf j))).totalDegree (hH0 j), ?_⟩
  have hres : ∀ D : BinaryRing K,
      (∀ i, D ∣ graphRestriction a b (residualFamily (f j) i)) → IsUnit D := by
    intro D hD
    have hle : U j ≤ (binaryDivisorSubspace D).comap (graphRestriction a b).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro P ⟨i, rfl⟩
      exact hD i
    exact (hpair j) (hle (hFU j)) (hle (hGU j))
  intro D
  constructor
  · intro hD
    apply product_common_divisor _ D (hH0 j)
      (fun i => graphRestriction a b (residualFamily (f j) i)) hres
    intro i
    simpa only [family_factorization (f j) i, map_mul] using hD i
  · intro hD i
    rw [family_factorization (f j) i, map_mul]
    exact dvd_mul_of_dvd_left hD _

end Cylinder.GcdGraphSelection
end
