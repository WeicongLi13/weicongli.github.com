module

public import Cylinder.NormalizedHyperbolaObstruction
public import Cylinder.ConicAffineMaps

/-! The actual hyperbola obstruction also holds for a scaled subgroup
coset. An explicit invertible diagonal map removes the coset parameter. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.NormalizedHyperbolaCosetObstruction

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks Cylinder.ProjectiveFieldEmbedding
open Cylinder.ConicAffineMaps Cylinder.ConicRootPairsGeometry
open Cylinder.NormalizedHyperbolaObstruction

variable {R K : Type*} [Field R] [Field K]

def rescaleCoordinates (a : Kˣ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  affineCoordinates (a : K)⁻¹ (a : K) 0 0 0 (inv_ne_zero (Units.ne_zero a)) (Units.ne_zero a)

theorem rescale_hyperbola (a t : Kˣ) :
    rescaleCoordinates a (hyperbolaVector (a * t)) = hyperbolaVector t := by
  ext i
  fin_cases i <;> simp [rescaleCoordinates, affineCoordinates, affineVector, hyperbolaVector,
    Units.val_mul, mul_inv_rev]
  calc
    (a : K) * ((t : K)⁻¹ * (a : K)⁻¹) = (t : K)⁻¹ * ((a : K) * (a : K)⁻¹) := by ring
    _ = (t : K)⁻¹ := by rw [mul_inv_cancel₀ (Units.ne_zero a), mul_one]

theorem subgroup_coset_card_le_four (A : NormalizedSystem R) (f : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (H : Subgroup Kˣ) [Finite H]
    (a : Kˣ) (c : K) (hc : c ≠ 0) (htwo : (2 : K) ≠ 0) (P : H → A.W)
    (hP : ∀ t : H, g (vectorMap f (A.E (P t))) = c • hyperbolaVector (a * t.val)) :
    Nat.card H ≤ 4 := by
  apply subgroup_card_le_four A f (g.trans (rescaleCoordinates a)) H c hc htwo P
  intro t
  change rescaleCoordinates a (g (vectorMap f (A.E (P t)))) = c • hyperbolaVector t.val
  rw [hP, map_smul, rescale_hyperbola]

theorem subgroup_coset_card_le_four_of_exists (A : NormalizedSystem R) (f : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (H : Subgroup Kˣ) [Finite H]
    (a : Kˣ) (c : K) (hc : c ≠ 0) (htwo : (2 : K) ≠ 0)
    (hP : ∀ t : H, ∃ P : A.W,
      g (vectorMap f (A.E P)) = c • hyperbolaVector (a * t.val)) : Nat.card H ≤ 4 :=
  subgroup_coset_card_le_four A f g H a c hc htwo (fun t => (hP t).choose)
    (fun t => (hP t).choose_spec)

end Cylinder.NormalizedHyperbolaCosetObstruction

end
