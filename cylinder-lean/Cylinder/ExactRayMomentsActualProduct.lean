module

public import Cylinder.ExactRayMomentsNormalization
public import Cylinder.ExactRayMomentsSupportedProduct
public import Cylinder.ExactRayMomentsBlackBalance
public import Cylinder.ProductProposition

/-! The original scaled white and weighted black products, in the actual
black-point coordinates. Every black direction is retained in the finite
direction type. The central black factor is exactly `T^weight(b)`. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsActualProduct
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection Cylinder.ProjectiveProjectionFibres
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsDirections
open Cylinder.ExactRayMomentsLow Cylinder.ExactRayMomentsMultiplicity
open Cylinder.ExactRayMomentsProduct Cylinder.ExactRayMomentsSupportedProduct
open Cylinder.ExactRayMomentsBlackBalance Cylinder.BlackProjectionVandermonde
open Cylinder.ProductFrobenius Cylinder.ProductRescaling
variable (p : ℕ) [Fact p.Prime]
local instance directionFintype : Fintype (BlackProjection.Direction p) := Fintype.ofFinite _

def whiteDirection {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : whitePoints p S) : BlackProjection.Direction p :=
  actualDirection p b H.val (ProjectiveLineCap.white_ne_black p H.property hb)

def blackDirection (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (H : (blackPoints p S).erase b) : BlackProjection.Direction p :=
  actualDirection p b H.val (Finset.mem_erase.mp H.property).1

theorem all_direction_representatives_distinct :
    Cylinder.HilbertEvaluation.ProjectivelyDistinct
      (fun d : BlackProjection.Direction p => d.rep) := by
  intro i k hik c heq
  have hmk := (Projectivization.mk_eq_mk_iff' (ZMod p) k.rep i.rep
    k.rep_nonzero i.rep_nonzero).mpr ⟨c, heq.symm⟩
  rw [Projectivization.mk_rep, Projectivization.mk_rep] at hmk
  exact hik hmk.symm

theorem all_direction_forms_prime :
    ∀ i : BlackProjection.Direction p, Prime (directionForm i.rep) :=
  fun i => directionForm_prime _ i.rep_nonzero

theorem all_direction_forms_not_dvd :
    ∀ i k : BlackProjection.Direction p, i ≠ k → ¬directionForm i.rep ∣ directionForm k.rep :=
  directionForms_not_dvd _ (fun i => i.rep_nonzero) (all_direction_representatives_distinct p)

theorem whiteDirection_projection {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (H : whitePoints p S) :
    whiteDirection p hb H = projection (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb) (whiteCoordinateEquiv p S H) := rfl

theorem blackDirection_mem_ray (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (H : (blackPoints p S).erase b) (i : BlackProjection.Direction p) :
    blackDirection p S b H = i ↔ H.val ∈ linePoints p (rayDualSpace p b i) := by
  rw [mem_linePoints, point_mem_rayDualSpace]
  exact (point_mem_raySpace (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H.val)
    (fun h => (Finset.mem_erase.mp H.property).1 (coordinatePoint_injective p h)) i).symm

theorem actual_black_product_in_coordinates {S : Finset (Geometry.Point p)}
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    productCoordinateMap p b
      (∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
      blackPolynomial (blackDirection p S b) (fun i => directionForm i.rep)
        (fun _ => (1 : ZMod p)) (fun H => normalizedTime p b H.val)
        (fun H => weight p S H.val) (weight p S b) := by
  simp only [map_prod, map_pow]
  rw [← Finset.mul_prod_erase (blackPoints p S)
    (fun H => productCoordinateMap p b (scaledPlaneForm p (normalizationScale p b) H) ^ weight p S H) hb,
    normalized_centre_factor]
  unfold blackPolynomial
  congr 1
  calc
    _ = ∏ H : (blackPoints p S).erase b,
      productCoordinateMap p b (scaledPlaneForm p (normalizationScale p b) H.val) ^ weight p S H.val :=
      (Finset.prod_coe_sort _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro H _
      rw [normalized_noncentral_factor p b H.val (Finset.mem_erase.mp H.property).1]
      simp only [blackDirection, map_one, one_mul]

theorem erased_subtype_product {A M : Type*} [DecidableEq A] [CommMonoid M]
    (s : Finset A) (e : s) (f : A → M) :
    (∏ x ∈ (Finset.univ : Finset s).erase e, f x.val) = ∏ x ∈ s.erase e.val, f x := by
  apply Finset.prod_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨hxe, _⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨fun h => hxe (Subtype.ext h), x.property⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨hye, hys⟩ := Finset.mem_erase.mp hy
    refine ⟨⟨y, hys⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    exact fun h => hye (congrArg Subtype.val h)
  · intro x _
    rfl

theorem actual_white_residue_in_coordinates {S : Finset (Geometry.Point p)}
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p) :
    productCoordinateMap p b
      (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H)) =
      actualNumerator (whiteDirection p hb) (fun i => directionForm i.rep)
        (fun H => c H.val) (fun H => normalizedTime p b H.val) := by
  simp only [map_sum, map_mul, productCoordinateMap_C, map_prod]
  rw [actualNumerator]
  calc
    _ = ∑ E : whitePoints p S, Polynomial.C (MvPolynomial.C (c E.val)) *
      ∏ H ∈ (whitePoints p S).erase E.val,
        productCoordinateMap p b (scaledPlaneForm p (normalizationScale p b) H) :=
      (Finset.sum_coe_sort _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E _
      congr 1
      rw [← erased_subtype_product (whitePoints p S) E]
      refine Finset.prod_congr (by ext H; simp) ?_
      intro H _
      exact normalized_noncentral_factor p b H.val
        (ProjectiveLineCap.white_ne_black p H.property hb)

end Cylinder.ExactRayMomentsActualProduct
end
