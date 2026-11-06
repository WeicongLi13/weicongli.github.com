module

public import Cylinder.BMMWhiteBlackLine
public import Cylinder.BMMLinearCoordinates
public import Cylinder.ConicRootPairsGeometry

/-! A genuine normalized white subsystem on one scaled hyperbola coset
has at most four parameters. The two black pair sums are obtained from
the original normalized sums, and transported back to the original
configuration before the white/black-line obstruction is applied. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.NormalizedHyperbolaObstruction

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMActualCoefficients
open Cylinder.BMMBlackLineBlocks Cylinder.BMMLinearCoordinates Cylinder.ProjectiveFieldEmbedding
open Cylinder.ConicRootPairsAlgebra Cylinder.ConicRootPairsGeometry Cylinder.FieldSubgroupCyclic

variable {R K : Type*} [Field R] [Field K]

def configuration (A : NormalizedSystem R) : Configuration R :=
  ⟨A.W, A.B, A.arc, A.disjoint, A.blocks, A.card⟩

theorem subgroup_card_le_four (A : NormalizedSystem R) (f : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (H : Subgroup Kˣ) [Finite H]
    (c : K) (hc : c ≠ 0) (htwo : (2 : K) ≠ 0) (P : H → A.W)
    (hP : ∀ t : H, g (vectorMap f (A.E (P t))) = c • hyperbolaVector t.val) :
    Nat.card H ≤ 4 := by
  by_contra hsmall
  have hm : 5 ≤ Nat.card H := by omega
  let v := (generator H).val
  have horder : 5 ≤ orderOf v := by rw [show orderOf v = Nat.card H from unit_generator_order H]; exact hm
  let v1 : H := generator H
  let vi : H := v1⁻¹
  let v2 : H := v1 ^ 2
  let v2i : H := v2⁻¹
  have hwhite : ∀ t : H, transformedPoint f g (P t).val = hyperbolaPoint t.val := by
    intro t
    obtain ⟨a, ha, hrep⟩ := A.representatives (P t)
    exact transformedPoint_eq_of_representative f g (P t).val (A.E (P t)) a ha hrep
      (hyperbolaVector t.val) (hyperbolaVector_nonzero t.val) c hc (hP t)
  have h1i : P v1 ≠ P vi := by
    intro h
    have hh := congrArg (fun Q : A.W => transformedPoint f g Q.val) h
    rw [hwhite, hwhite] at hh
    exact inverse_pair_distinct v horder hh
  have h2i : P v2 ≠ P v2i := by
    intro h
    have hh := congrArg (fun Q : A.W => transformedPoint f g Q.val) h
    rw [hwhite, hwhite] at hh
    exact inverse_square_pair_distinct v horder hh
  let R1 : A.B := blocker A (P v1) (P vi) h1i
  let R2 : A.B := blocker A (P v2) (P v2i) h2i
  have hsum1 : g (vectorMap f (A.E (P v1) + A.E (P vi))) = c • pairVector v := by
    rw [map_add, map_add, hP, hP, ← smul_add]
    exact congrArg (fun z : Fin 3 → K => c • z) (hyperbola_pair_sum v)
  have hsum2 : g (vectorMap f (A.E (P v2) + A.E (P v2i))) = c • squarePairVector v := by
    rw [map_add, map_add, hP, hP, ← smul_add]
    exact congrArg (fun z : Fin 3 → K => c • z) (hyperbola_square_pair_sum v)
  have hR1 : transformedPoint f g R1.val = pairPoint v htwo := by
    obtain ⟨a, ha, hrep⟩ := A.sums (P v1) (P vi) h1i
    exact transformedPoint_eq_of_representative f g R1.val (A.E (P v1) + A.E (P vi))
      a ha hrep (pairVector v) (pairVector_nonzero v htwo) c hc hsum1
  have hR2 : transformedPoint f g R2.val = squarePairPoint v htwo := by
    obtain ⟨a, ha, hrep⟩ := A.sums (P v2) (P v2i) h2i
    exact transformedPoint_eq_of_representative f g R2.val (A.E (P v2) + A.E (P v2i))
      a ha hrep (squarePairVector v) (squarePairVector_nonzero v htwo) c hc hsum2
  have hRs : R1 ≠ R2 := by
    intro h
    have hh := congrArg (fun Q : A.B => transformedPoint f g Q.val) h
    rw [hR1, hR2] at hh
    exact pair_points_distinct v horder htwo hh
  have hP0 : transformedPoint f g (P (1 : H)).val = whitePoint K := by
    rw [hwhite]
    exact hyperbola_one_point
  have hPR : (P (1 : H)).val ≠ R1.val := by
    intro h
    exact Finset.disjoint_left.mp A.disjoint (P (1 : H)).property (h ▸ R1.property)
  have hcol' : Collinear (transformedPoint f g (P (1 : H)).val)
      (transformedPoint f g R1.val) (transformedPoint f g R2.val) := by
    rw [hP0, hR1, hR2]
    exact pair_points_collinear v htwo
  have hcol := (transformedPoint_collinear_iff f g (P (1 : H)).val R1.val R2.val hPR).mp hcol'
  exact BMMWhiteBlackLine.not_collinear_white_two_black (configuration A) (P (1 : H)) R1 R2 hRs hcol

end Cylinder.NormalizedHyperbolaObstruction

end
