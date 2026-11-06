module

public import Cylinder.ExactRayMomentsActualBalance

/-! Low moments and the first nonzero moment for the actual normalized
product residues of a p-divisible point set. The product identity and all
direction multiplicities are derived from the original geometric data. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsActual
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsDirections
open Cylinder.ExactRayMomentsLow Cylinder.ExactRayMomentsMultiplicity
open Cylinder.ExactRayMomentsProduct Cylinder.ExactRayMomentsSupportedProduct
open Cylinder.ExactRayMomentsActualProduct Cylinder.ExactRayMomentsActualBalance
open Cylinder.ProductFrobenius Cylinder.ProductRescaling
variable (p : ℕ) [Fact p.Prime]
local instance directionFintype : Fintype (BlackProjection.Direction p) := Fintype.ofFinite _

theorem exists_actual_exact_moments {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : DualPoint p → ZMod p,
      (∀ H ∈ whitePoints p S, c H ≠ 0) ∧
      ((∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
        ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
          ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H) ∧
      ((∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        scaledPlaneForm p (normalizationScale p b) E ^ (p - 2)) = 0) ∧
      (∀ j, j < weight p S b → ∀ i : BlackProjection.Direction p,
        moment (whiteDirection p hb) (fun H => c H.val) (fun H => normalizedTime p b H.val) i j = 0) ∧
      (∀ i : BlackProjection.directionSet p S b hb,
        moment (whiteDirection p hb) (fun H => c H.val) (fun H => normalizedTime p b H.val)
          i.val (weight p S b) ≠ 0) := by
  obtain ⟨c, hc, hprod, _hfrac, hpower, _hcK, _hrel⟩ :=
    Cylinder.ProductProposition.scaled_product_and_full_support_relation p (K := ZMod p) hcard hS
      (normalizationScale p b) (fun H _ => normalizationScale_nonzero p b H)
      (fun H _ => normalizationScale_nonzero p b H)
  let P := blackPolynomial (blackDirection p S b) (fun i => directionForm i.rep)
    (fun _ => (1 : ZMod p)) (fun H => normalizedTime p b H.val)
    (fun H => weight p S H.val) (weight p S b)
  have hprodP : P = actualNumerator (whiteDirection p hb) (fun i => directionForm i.rep)
      (fun H => c H.val) (fun H => normalizedTime p b H.val) := by
    calc
      P = productCoordinateMap p b
          (∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) :=
        (actual_black_product_in_coordinates p hb).symm
      _ = _ := congrArg (productCoordinateMap p b) hprod
      _ = _ := actual_white_residue_in_coordinates p hb c
  have hmoment := supported_balanced_product_exact_moments
    (whiteDirection p hb) (blackDirection p S b) (fun i => directionForm i.rep)
    (all_direction_forms_prime p) (all_direction_forms_not_dvd p)
    (fun H => c H.val) (fun H => normalizedTime p b H.val)
    (fun _ => (1 : ZMod p)) (fun H => normalizedTime p b H.val) (fun _ => one_ne_zero)
    (fun H => weight p S H.val) (weight p S b) P hprodP rfl
    (supported_actual_weight_balance p hcard hS hb)
  refine ⟨c, hc, hprod, hpower, hmoment.1, ?_⟩
  intro i
  apply hmoment.2 i.val
  rw [white_exponent_eq_raySize p hb i]
  exact raySize_pos (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) i

end Cylinder.ExactRayMomentsActual
end
